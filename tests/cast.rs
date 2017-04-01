extern crate cast;
extern crate fpa;

use cast::*;
use fpa::*;

include!(concat!(env!("OUT_DIR"), "/cross.rs"));

include!(concat!(env!("OUT_DIR"), "/to-ixx.rs"));

include!(concat!(env!("OUT_DIR"), "/from-ixx.rs"));
