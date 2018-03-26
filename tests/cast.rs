extern crate cast;
extern crate fpa;

#[cfg(test)]
mod cross {
    use cast::*;
    use fpa::*;

    include!(concat!(env!("OUT_DIR"), "/cross.rs"));
}

#[cfg(test)]
mod to {
    use cast::*;
    use fpa::*;

    include!(concat!(env!("OUT_DIR"), "/to-ixx.rs"));
}

#[cfg(test)]
mod from {
    use cast::*;
    use fpa::*;

    include!(concat!(env!("OUT_DIR"), "/from-ixx.rs"));
}
