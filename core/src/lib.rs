// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This library exposes a low-level API for creating your own efficient
//! synchronization primitives.
//!
//! # The parking lot
//!
//! To keep synchronization primitives small, all thread queuing and suspending
//! functionality is offloaded to the *parking lot*. The idea behind this is based
//! on the Webkit [`WTF::ParkingLot`](https://webkit.org/blog/6161/locking-in-webkit/)
//! class, which essentially consists of a hash table mapping of lock addresses
//! to queues of parked (sleeping) threads. The Webkit parking lot was itself
//! inspired by Linux [futexes](http://man7.org/linux/man-pages/man2/futex.2.html),
//! but it is more powerful since it allows invoking callbacks while holding a
//! queue lock.
//!
//! There are two main operations that can be performed on the parking lot:
//!
//!  - *Parking* refers to suspending the thread while simultaneously enqueuing it
//! on a queue keyed by some address.
//! - *Unparking* refers to dequeuing a thread from a queue keyed by some address
//! and resuming it.
//!
//! See the documentation of the individual functions for more details.
//!
//! # Building custom synchronization primitives
//!
//! Building custom synchronization primitives is very simple since the parking
//! lot takes care of all the hard parts for you. A simple example for a
//! custom primitive would be to integrate a `Mutex` inside another data type.
//! Since a mutex only requires 2 bits, it can share space with other data.
//! For example, one could create an `ArcMutex` type that combines the atomic
//! reference count and the two mutex bits in the same atomic word.

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![cfg_attr(
    all(target_env = "sgx", target_vendor = "fortanix"),
    feature(sgx_platform)
)]
#![cfg_attr(
    all(
        feature = "nightly",
        target_family = "wasm",
        target_feature = "atomics"
    ),
    feature(stdarch_wasm_atomic_wait)
)]

mod parking_lot;
mod spinwait;
mod thread_parker;
mod util;
mod word_lock;

pub use self::parking_lot::deadlock;
pub use self::parking_lot::{park, unpark_all, unpark_filter, unpark_one, unpark_requeue};
pub use self::parking_lot::{
    FilterOp, ParkResult, ParkToken, RequeueOp, UnparkResult, UnparkToken,
};
pub use self::parking_lot::{DEFAULT_PARK_TOKEN, DEFAULT_UNPARK_TOKEN};
pub use self::spinwait::SpinWait;

pub(crate) static SHARED_OBJECT_ID: u64 = 0;

// format as hex!
pub(crate) fn shared_object_id() -> u64 {
    &SHARED_OBJECT_ID as *const _ as u64
}

#[cfg(feature = "import-globals")]
pub(crate) static GLOBAL_MODE: &str = "I";

#[cfg(feature = "export-globals")]
pub(crate) static GLOBAL_MODE: &str = "E";

#[cfg(not(any(feature = "import-globals", feature = "export-globals")))]
pub(crate) static GLOBAL_MODE: &str = "N";

#[cfg(all(feature = "import-globals", feature = "export-globals"))]
compile_error!("The features \"import-globals\" and \"export-globals\" are mutually exclusive");

/// Represents a color generated from a u64 value.
pub(crate) struct AddrColor<'a> {
    fg: (u8, u8, u8),
    bg: (u8, u8, u8),
    extra: &'a str,
    val: u64,
}

impl<'a> AddrColor<'a> {
    pub(crate) fn new(extra: &'a str, u: u64) -> Self {
        fn hash(mut x: u64) -> u64 {
            const K: u64 = 0x517cc1b727220a95;
            x = x.wrapping_mul(K);
            x ^= x >> 32;
            x = x.wrapping_mul(K);
            x ^= x >> 32;
            x = x.wrapping_mul(K);
            x
        }

        let hashed_float = (hash(u) as f64) / (u64::MAX as f64);
        let h = hashed_float * 360.0;
        let s = 50.0;
        let l = 70.0;

        fn hsl_to_rgb(h: f64, s: f64, l: f64) -> (u8, u8, u8) {
            let h = h / 360.0;
            let s = s / 100.0;
            let l = l / 100.0;

            let c = (1.0 - (2.0 * l - 1.0).abs()) * s;
            let x = c * (1.0 - ((h * 6.0) % 2.0 - 1.0).abs());
            let m = l - c / 2.0;

            let (r, g, b) = match (h * 6.0) as u8 {
                0 | 6 => (c, x, 0.0),
                1 => (x, c, 0.0),
                2 => (0.0, c, x),
                3 => (0.0, x, c),
                4 => (x, 0.0, c),
                _ => (c, 0.0, x),
            };

            (
                ((r + m) * 255.0) as u8,
                ((g + m) * 255.0) as u8,
                ((b + m) * 255.0) as u8,
            )
        }

        let fg = hsl_to_rgb(h, s, l);
        let bg = hsl_to_rgb(h, s * 0.8, l * 0.5);

        Self {
            fg,
            bg,
            extra,
            val: u,
        }
    }
}

impl<'a> std::fmt::Display for AddrColor<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "\x1b[48;2;{};{};{}m\x1b[38;2;{};{};{}m{}#{:0x}\x1b[0m",
            self.bg.0, self.bg.1, self.bg.2, self.fg.0, self.fg.1, self.fg.2, self.extra, self.val
        )
    }
}

/// Prints a message with the current shared object id.
#[macro_export]
macro_rules! soprintln {
    ($($arg:tt)*) => {
        {
            let id = $crate::shared_object_id();
            let color = $crate::AddrColor::new($crate::GLOBAL_MODE, id);
            let curr_thread = std::thread::current();
            let tid = format!("{:?}", curr_thread.id());
            // strip `ThreadId(` prefix
            let tid = tid.strip_prefix("ThreadId(").unwrap_or(&tid);
            // strip `)` suffix
            let tid = tid.strip_suffix(")").unwrap_or(&tid);
            // parse tid as u64
            let tid = tid.parse::<u64>().unwrap_or(0);
            let thread_name = curr_thread.name().unwrap_or("<unnamed>");
            let thread = $crate::AddrColor::new(thread_name, tid);

            let timestamp = ::std::time::SystemTime::now().duration_since(::std::time::UNIX_EPOCH).unwrap().as_millis() % 99999;
            let msg = format!($($arg)*);
            eprintln!("{timestamp:05} {color} {thread} {msg}");
        }
    };
}
