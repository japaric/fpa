#![cfg_attr(feature = "try-from", feature(try_from))]

extern crate cast;
extern crate fpa;

use cast::*;
use fpa::*;

#[allow(unused_imports)]
#[cfg(feature = "try-from")]
use std::convert::TryFrom;

#[cfg(test)]
mod cross {
    use super::*;

    include!(concat!(env!("OUT_DIR"), "/cross.rs"));
}

#[cfg(test)]
mod to {
    use super::*;

    include!(concat!(env!("OUT_DIR"), "/to-ixx.rs"));
}

#[cfg(test)]
mod from {
    use super::*;

    include!(concat!(env!("OUT_DIR"), "/from-ixx.rs"));
}
