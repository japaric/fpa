//! Fixed Point Arithmetic
//!
//! # Naming convention
//!
//! There are unsigned fixed point types, like `UFmPn`, and signed ones, like
//! `FmPn`. The `m` in the name indicates the number of bits used to store the
//! integral part of the number and `n` indicates the number of bits used for
//! the fractional part.
//!
//! # Range and precision
//!
//! The type `UFmPn` can store numbers in the range `[0, 2^m - 2^-n]` with a
//! precision of `2^-n`.
//!
//! The type `FmPn` can store numbers in the range `[-2^(m-1), 2^(m-1) - 2^-n]`
//! with a precision of `2^-n`.
//!
//! # Initialization
//!
//! If you have enabled the `const-fn` Cargo feature, you can initialize
//! fixed point numbers in "const context" using the `new` constructor.
//!
//! ```
//! #![feature(const_fn)]
//!
//! use fpa::F1P7;
//!
//! const K: F1P7 = F1P7::new(0.5);
//! ```
//!
//! # Casting
//!
//! Otherwise you can cast a floating point value into a fixed point format.
//!
//! ```
//! use fpa::F1P7;
//!
//! assert!(F1P7(0.5_f64).is_ok());
//! assert!(F1P7(1.5_f64).is_err());
//! ```
//!
//! Note that, in this case, the cast operation is fallible because the original
//! number may not fit in the destination type.
//!
//! But infallible cast operations, from small integers, also exist.
//!
//! ```
//! use fpa::F16P16;
//!
//! assert_eq!(F16P16(1_i16) + F16P16(-1_i16), F16P16(0_i16));
//! ```
//!
//! # Arithmetic
//!
//! All the types support addition, subtraction, multiplication and division.
//!
//! # Formatting
//!
//! All the types support sprintf-style formatting so you can format a number
//! directly into a buffer without requiring heap allocation or a write
//! operation.
//!
//! ```
//! #![feature(const_fn)]
//!
//! use fpa::F1P7;
//!
//! assert_eq!(&*F1P7::new(0.25).fmt(&mut [0; 10]), "0.25")
//! ```

#![cfg_attr(feature = "const-fn", feature(const_fn))]
#![deny(missing_docs)]
#![deny(warnings)]
#![no_std]

extern crate cast;
extern crate numtoa;
#[cfg(test)]
#[macro_use]
extern crate std;

use core::{fmt, slice, str, i16, i32, i8, u8, u16, u32};
use core::ops;

use cast::{Error, f32, f64, i8, i16, i32, i64, isize, u8, u16, u32, u64, usize};
use numtoa::NumToA;

#[cfg(test)]
mod tests;

/// Range: `[-32768.0, 32768.0 - 2^-16]`. Precision: `2^-16`
pub mod f16p16 {
    /// Largest value that can be represented by this type
    pub const MAX: ::F16P16 = ::F16P16 { bits: ::core::i32::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::F16P16 = ::F16P16 { bits: ::core::i32::MIN };
}

/// Range: `[-1.0, 1.0 - 2^-15]`. Precision: `2^-15`
pub mod f1p15 {
    /// Largest value that can be represented by this type
    pub const MAX: ::F1P15 = ::F1P15 { bits: ::core::i16::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::F1P15 = ::F1P15 { bits: ::core::i16::MIN };
}

/// Range: `[-1.0, 1.0 - 2^-7]`. Precision: `2^-7`
pub mod f1p7 {
    /// Largest value that can be represented by this type
    pub const MAX: ::F1P7 = ::F1P7 { bits: ::core::i8::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::F1P7 = ::F1P7 { bits: ::core::i8::MIN };
}

/// Range: `[-8388608.0, 8388608.0 - 2^-8]`. Precision: `2^-8`
pub mod f24p8 {
    /// Largest value that can be represented by this type
    pub const MAX: ::F24P8 = ::F24P8 { bits: ::core::i32::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::F24P8 = ::F24P8 { bits: ::core::i32::MIN };
}

/// Range: `[0.0, 1.0 - 2^-16]`. Precision: `2^-16`
pub mod uf0p16 {
    /// Largest value that can be represented by this type
    pub const MAX: ::UF0P16 = ::UF0P16 { bits: ::core::u16::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::UF0P16 = ::UF0P16 { bits: ::core::u16::MIN };
}

/// Range: `[0.0, 1.0 - 2^-8]`. Precision: `2^-8`
pub mod uf0p8 {
    /// Largest value that can be represented by this type
    pub const MAX: ::UF0P8 = ::UF0P8 { bits: ::core::u8::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::UF0P8 = ::UF0P8 { bits: ::core::u8::MIN };
}

/// Range: `[0.0, 65536.0 - 2^-16]`. Precision: `2^-16`
pub mod uf16p16 {
    /// Largest value that can be represented by this type
    pub const MAX: ::UF16P16 = ::UF16P16 { bits: ::core::u32::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::UF16P16 = ::UF16P16 { bits: ::core::u32::MIN };
}

/// Range: `[0.0, 16777216.0 - 2^-8]`. Precision: `2^-8`
pub mod uf24p8 {
    /// Largest value that can be represented by this type
    pub const MAX: ::UF24P8 = ::UF24P8 { bits: ::core::u32::MAX };

    /// Smallest value that can be represented by this type
    pub const MIN: ::UF24P8 = ::UF24P8 { bits: ::core::u32::MIN };
}

static DIGITS: [u8; 10] = [b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7',
                           b'8', b'9'];

macro_rules! add {
    ($self:ident) => {
        impl ops::Add for $self {
            type Output = $self;

            fn add(self, rhs: Self) -> Self {
                $self { bits: self.bits + rhs.bits }
            }
        }

        impl ops::AddAssign for $self {
            fn add_assign(&mut self, rhs: Self) {
                self.bits += rhs.bits;
            }
        }
    }
}

macro_rules! add_int {
    ($self:ident, $N:expr, $int:ident, $repr:ident) => {
        impl ops::Add<$int> for $self {
            type Output = Self;

            fn add(self, rhs: $int) -> Self {
                $self { bits: self.bits + $repr(rhs) << $N }
            }
        }

        impl ops::Add<$self> for $int {
            type Output = $self;

            fn add(self, rhs: $self) -> $self {
                rhs + self
            }
        }

        impl ops::AddAssign<$int> for $self {
            fn add_assign(&mut self, rhs: $int) {
                self.bits += $repr(rhs) << $N;
            }
        }
    }
}

macro_rules! div {
    ($self:ident, $N:expr, $upscale:ident, $repr:ident) => {
        impl ops::Div for $self {
            type Output = Self;

            fn div(self, rhs: Self) -> Self {
                let d = ($upscale(self.bits) << $N) / $upscale(rhs.bits);
                $self {
                    bits: match $repr(d) {
                        #[cfg(debug_assertions)]
                        Err(_) => panic!("attempt to divide with overflow"),
                        #[cfg(not(debug_assertions))]
                        Err(_) => d as $repr,
                        Ok(d) => d,
                    }
                }
            }
        }
    }
}

macro_rules! mul {
    ($self:ident, $N:expr, $upscale:ident, $repr:ident) => {
        impl ops::Mul for $self {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self {
                $self {
                    bits: ($upscale(self.bits) *
                           $upscale(rhs.bits) >> $N) as $repr
                }
            }
        }
    }
}

macro_rules! mul_overflow {
    ($self:ident, $N:expr, $upscale:ident, $repr:ident) => {
        impl ops::Mul for $self {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self {
                let p = $upscale(self.bits) * $upscale(rhs.bits) >> $N;
                $self {
                    bits: match $repr(p) {
                        #[cfg(debug_assertions)]
                        Err(_) => panic!("attempt to multiply with overflow"),
                        #[cfg(not(debug_assertions))]
                        Err(_) => p as $repr,
                        Ok(p) => p,
                    }
                }
            }
        }
    }
}

macro_rules! scale {
    ($self:ident, $repr:ident) => {
        impl ops::Div<$repr> for $self {
            type Output = Self;

            fn div(self, rhs: $repr) -> Self {
                $self { bits: self.bits / rhs }
            }
        }

        impl ops::DivAssign<$repr> for $self {
            fn div_assign(&mut self, rhs: $repr) {
                self.bits /= rhs;
            }
        }

        impl ops::Mul<$self> for $repr {
            type Output = $self;

            fn mul(self, rhs: $self) -> $self {
                $self { bits: rhs.bits * self }
            }
        }

        impl ops::Mul<$repr> for $self {
            type Output = Self;

            fn mul(self, rhs: $repr) -> Self {
                $self { bits: self.bits * rhs }
            }
        }

        impl ops::MulAssign<$repr> for $self {
            fn mul_assign(&mut self, rhs: $repr) {
                self.bits *= rhs;
            }
        }

    }
}

macro_rules! shift {
    ($self:ident ($($shift:ident),+)) => {
        $(
            impl ops::Shl<$shift> for $self {
                type Output = Self;

                fn shl(self, rhs: $shift) -> Self {
                    $self { bits: self.bits << rhs }
                }
            }

            impl ops::Shr<$shift> for $self {
                type Output = Self;

                fn shr(self, rhs: $shift) -> Self {
                    $self { bits: self.bits >> rhs }
                }
            }
        )+
    }
}

macro_rules! sub {
    ($self:ident) => {
        impl ops::Sub for $self {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self {
                $self { bits: self.bits - rhs.bits }
            }
        }

        impl ops::SubAssign for $self {
            fn sub_assign(&mut self, rhs: Self) {
                self.bits -= rhs.bits;
            }
        }
    }
}

macro_rules! sub_int {
    ($self:ident, $N:expr, $int:ident, $repr:ident) => {
        impl ops::Sub<$int> for $self {
            type Output = Self;

            fn sub(self, rhs: $int) -> Self {
                $self { bits: self.bits - $repr(rhs) << $N}
            }
        }

        impl ops::Sub<$self> for $int {
            type Output = $self;

            fn sub(self, rhs: $self) -> $self {
                $self { bits: ($repr(self) << $N) - rhs.bits }
            }
        }

        impl ops::SubAssign<$int> for $self {
            fn sub_assign(&mut self, rhs: $int) {
                self.bits -= $repr(rhs) << $N;
            }
        }
    }
}

/// Range: `[-32768.0, 32768.0 - 2^-16]`. Precision: `2^-16`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct F16P16 {
    bits: i32,
}

impl F16P16 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        F16P16 { bits: (x * (1 << 16) as f64) as i32 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 23]) -> Str<'s> {
        const DIVISOR: u32 = 1 << 16;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 6;

        if self.bits == i32::MIN {
            const S: &'static [u8] = b"-32768";

            buffer[..S.len()].copy_from_slice(S);

            return Str {
                       start: 0,
                       end: S.len(),
                       s: unsafe { mk_str(buffer.as_ptr(), S.len()) },
                   };
        }

        let mut int = (self.bits.abs() >> 16) as i16;
        if self.bits < 0 {
            int = -int
        }
        let mut start = int.numtoa(10, &mut buffer[..6]);
        if self.bits < 0 && int == 0 {
            start -= 1;
            buffer[start] = b'-';
        }

        let frac = u32(self.bits.abs() as u16);

        if frac == 0 {
            return Str {
                       start: start,
                       end: SPLIT,
                       s: unsafe {
                           mk_str(buffer.as_ptr().offset(start as isize),
                                  SPLIT - start)
                       },
                   };
        }

        buffer[SPLIT] = b'.';

        let end = unsafe {
            fmt32(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  frac,
                  DIVISOR)
        };

        unsafe {
            Str {
                start: start,
                end: SPLIT + end + 1,
                s: mk_str(buffer.as_ptr().offset(start as isize),
                          end + SPLIT + 1 - start),
            }
        }
    }

    /// Creates a `F16P16` from raw bits
    pub fn from_raw_bits(bits: i32) -> Self {
        F16P16 { bits: bits }
    }

    /// Turns `F16P16` into raw bits
    pub fn into_raw_bits(&self) -> i32 {
        self.bits
    }
}

impl cast::From<F16P16> for F16P16 {
    type Output = F16P16;

    fn cast(x: F16P16) -> Self::Output {
        x
    }
}

impl cast::From<F1P7> for F16P16 {
    type Output = F16P16;

    fn cast(x: F1P7) -> Self::Output {
        F16P16 { bits: i32(x.bits) << 9 }
    }
}

impl cast::From<F1P15> for F16P16 {
    type Output = F16P16;

    fn cast(x: F1P15) -> Self::Output {
        F16P16 { bits: i32(x.bits) << 1 }
    }
}

impl cast::From<F24P8> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: F24P8) -> Self::Output {
        i32(i64(x.bits) << 8).map(|b| F16P16 { bits: b })
    }
}

impl cast::From<UF0P16> for F16P16 {
    type Output = F16P16;

    fn cast(x: UF0P16) -> Self::Output {
        F16P16 { bits: i32(x.bits) }
    }
}

impl cast::From<UF0P8> for F16P16 {
    type Output = F16P16;

    fn cast(x: UF0P8) -> Self::Output {
        F16P16 { bits: i32(x.bits) << 8 }
    }
}

impl cast::From<UF16P16> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        i32(x.bits).map(|b| F16P16 { bits: b })
    }
}

impl cast::From<UF24P8> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i32(u64(x.bits) << 8).map(|b| F16P16 { bits: b })
    }
}

impl cast::From<f32> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: f32) -> Self::Output {
        i32(x * (1 << 16) as f32).map(|b| F16P16 { bits: b })
    }
}

impl cast::From<f64> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: f64) -> Self::Output {
        i32(x * (1 << 16) as f64).map(|b| F16P16 { bits: b })
    }
}

impl cast::From<i8> for F16P16 {
    type Output = F16P16;

    fn cast(x: i8) -> Self::Output {
        F16P16(i16(x))
    }
}

impl cast::From<i16> for F16P16 {
    type Output = F16P16;

    fn cast(x: i16) -> Self::Output {
        F16P16 { bits: i32(x) << 16 }
    }
}

impl cast::From<i32> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: i32) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<i64> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: i64) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<isize> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: isize) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<u8> for F16P16 {
    type Output = F16P16;

    fn cast(x: u8) -> Self::Output {
        F16P16(i16(x))
    }
}

impl cast::From<u16> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: u16) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<u32> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: u32) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<u64> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: u64) -> Self::Output {
        i16(x).map(F16P16)
    }
}

impl cast::From<usize> for F16P16 {
    type Output = Result<F16P16, Error>;

    fn cast(x: usize) -> Self::Output {
        i16(x).map(F16P16)
    }
}

// NOTE handled above
// impl cast::From<F16P16> for F16P16 {}

impl cast::From<F16P16> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: F16P16) -> Self::Output {
        i16(x.bits >> 1).map(|b| F1P15 { bits: b })
    }
}

impl cast::From<F16P16> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: F16P16) -> Self::Output {
        i8(x.bits >> 9).map(|b| F1P7 { bits: b })
    }
}

impl cast::From<F16P16> for F24P8 {
    type Output = F24P8;

    fn cast(x: F16P16) -> Self::Output {
        F24P8 { bits: x.bits >> 8 }
    }
}

impl cast::From<F16P16> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u16(x.bits).map(|b| UF0P16 { bits: b })
    }
}

impl cast::From<F16P16> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u8(x.bits >> 8).map(|b| UF0P8 { bits: b })
    }
}

impl cast::From<F16P16> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u32(x.bits).map(|b| UF16P16 { bits: b })
    }
}

impl cast::From<F16P16> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u32(x.bits >> 8).map(|b| UF24P8 { bits: b })
    }
}

impl cast::From<F16P16> for f32 {
    type Output = f32;

    fn cast(x: F16P16) -> Self::Output {
        f32(x.bits) / f32(1 << 16)
    }
}

impl cast::From<F16P16> for f64 {
    type Output = f64;

    fn cast(x: F16P16) -> Self::Output {
        f64(x.bits) / f64(1 << 16)
    }
}

impl cast::From<F16P16> for i8 {
    type Output = Result<i8, Error>;

    fn cast(x: F16P16) -> Self::Output {
        i8(i16(x))
    }
}

impl cast::From<F16P16> for i16 {
    type Output = i16;

    fn cast(x: F16P16) -> Self::Output {
        (x.bits >> 16) as i16
    }
}

impl cast::From<F16P16> for i32 {
    type Output = i32;

    fn cast(x: F16P16) -> Self::Output {
        i32(i16(x))
    }
}

impl cast::From<F16P16> for i64 {
    type Output = i64;

    fn cast(x: F16P16) -> Self::Output {
        i64(i16(x))
    }
}

impl cast::From<F16P16> for isize {
    type Output = isize;

    fn cast(x: F16P16) -> Self::Output {
        isize(i16(x))
    }
}

impl cast::From<F16P16> for u8 {
    type Output = Result<u8, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u8(i16(x))
    }
}

impl cast::From<F16P16> for u16 {
    type Output = Result<u16, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u16(i16(x))
    }
}

impl cast::From<F16P16> for u32 {
    type Output = Result<u32, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u32(i32(x))
    }
}

impl cast::From<F16P16> for u64 {
    type Output = Result<u64, Error>;

    fn cast(x: F16P16) -> Self::Output {
        u64(i64(x))
    }
}

impl cast::From<F16P16> for usize {
    type Output = Result<usize, Error>;

    fn cast(x: F16P16) -> Self::Output {
        usize(isize(x))
    }
}

impl fmt::Display for F16P16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 23]))
    }
}

add!(F16P16);

add_int!(F16P16, 16, i16, i32);

div!(F16P16, 16, i64, i32);

mul_overflow!(F16P16, 16, i64, i32);

scale!(F16P16, i32);

shift!(F16P16(u8, u16, u32, u64, usize));

sub!(F16P16);

sub_int!(F16P16, 16, i16, i32);

/// Range: `[-1.0, 1.0 - 2^-15]`. Precision: `2^-15`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct F1P15 {
    bits: i16,
}

impl F1P15 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        F1P15 { bits: (x * (1 << 15) as f64) as i16 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 18]) -> Str<'s> {
        const DIVISOR: u32 = 1 << 15;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 2;

        if self.bits == 0 {
            buffer[0] = b'0';

            return Str {
                       start: 0,
                       end: 1,
                       s: unsafe { mk_str(buffer.as_ptr(), 1) },
                   };
        } else if self.bits == i16::MIN {
            buffer[0] = b'-';
            buffer[1] = b'1';

            return Str {
                       start: 0,
                       end: 2,
                       s: unsafe { mk_str(buffer.as_ptr(), 2) },
                   };
        }

        buffer[1] = b'0';
        buffer[2] = b'.';

        let (bits, offset) = if self.bits < 0 {
            buffer[0] = b'-';
            (-self.bits, 0)
        } else {
            (self.bits, 1)
        };
        let i = unsafe {
            fmt32(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  bits as u32,
                  DIVISOR)
        };

        Str {
            start: offset as usize,
            end: i + SPLIT + 1,
            s: unsafe {
                mk_str(buffer.as_ptr().offset(offset),
                       i + SPLIT + 1 - offset as usize)
            },
        }
    }

    /// Creates a `F1P15` from raw bits
    pub fn from_raw_bits(bits: i16) -> Self {
        F1P15 { bits: bits }
    }

    /// Turns `F1P15` into raw bits
    pub fn into_raw_bits(&self) -> i16 {
        self.bits
    }
}

impl cast::From<F1P15> for F1P15 {
    type Output = F1P15;

    fn cast(x: F1P15) -> Self::Output {
        x
    }
}

impl cast::From<F1P7> for F1P15 {
    type Output = F1P15;

    fn cast(x: F1P7) -> Self::Output {
        F1P15 { bits: i16(x.bits) << 8 }
    }
}

impl cast::From<UF0P8> for F1P15 {
    type Output = F1P15;

    fn cast(x: UF0P8) -> Self::Output {
        F1P15 { bits: i16(x.bits) << 7 }
    }
}

impl cast::From<UF0P16> for F1P15 {
    type Output = F1P15;

    fn cast(x: UF0P16) -> Self::Output {
        F1P15 { bits: (x.bits >> 1) as i16 }
    }
}

impl cast::From<f32> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: f32) -> Self::Output {
        i16(x * (1 << 15) as f32).map(|b| F1P15 { bits: b })
    }
}

impl cast::From<f64> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: f64) -> Self::Output {
        i16(x * (1 << 15) as f64).map(|b| F1P15 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<F1P15> for F16P16 {}
// impl cast::From<F1P15> for F1P15 {}

impl cast::From<F1P15> for F1P7 {
    type Output = F1P7;

    fn cast(x: F1P15) -> Self::Output {
        F1P7 { bits: (x.bits >> 8) as i8 }
    }
}

impl cast::From<F1P15> for F24P8 {
    type Output = F24P8;

    fn cast(x: F1P15) -> Self::Output {
        F24P8 { bits: i32(x.bits) >> 7 }
    }
}

impl cast::From<F1P15> for f32 {
    type Output = f32;

    fn cast(x: F1P15) -> Self::Output {
        f32(x.bits) / f32(1 << 15)
    }
}

impl cast::From<F1P15> for f64 {
    type Output = f64;

    fn cast(x: F1P15) -> Self::Output {
        f64(x.bits) / f64(1 << 15)
    }
}

impl fmt::Display for F1P15 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 18]))
    }
}

add!(F1P15);

div!(F1P15, 15, i32, i16);

mul!(F1P15, 15, i32, i16);

scale!(F1P15, i16);

shift!(F1P15(u8, u16, u32, u64, usize));

sub!(F1P15);

/// Range: `[-1.0, 1.0 - 2^-7]`. Precision: `2^-7`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct F1P7 {
    bits: i8,
}

impl F1P7 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        F1P7 { bits: (x * (1 << 7) as f64) as i8 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 10]) -> Str<'s> {
        const DIVISOR: u16 = 1 << 7;
        const SPLIT: usize = 2;

        if self.bits == 0 {
            buffer[0] = b'0';

            return Str {
                       start: 0,
                       end: 1,
                       s: unsafe { mk_str(buffer.as_ptr(), 1) },
                   };
        } else if self.bits == i8::MIN {
            buffer[0] = b'-';
            buffer[1] = b'1';

            return Str {
                       start: 0,
                       end: 2,
                       s: unsafe { mk_str(buffer.as_ptr(), 2) },
                   };
        }

        buffer[1] = b'0';
        buffer[2] = b'.';

        let (bits, offset) = if self.bits < 0 {
            buffer[0] = b'-';
            (-self.bits, 0)
        } else {
            (self.bits, 1)
        };
        let i = unsafe {
            fmt16(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  bits as u16,
                  DIVISOR)
        };

        Str {
            start: offset as usize,
            end: i + SPLIT + 1,
            s: unsafe {
                mk_str(buffer.as_ptr().offset(offset),
                       i + SPLIT + 1 - offset as usize)
            },
        }
    }

    /// Creates a `F1P7` from raw bits
    pub fn from_raw_bits(bits: i8) -> Self {
        F1P7 { bits: bits }
    }

    /// Turns `F1P7` into raw bits
    pub fn into_raw_bits(&self) -> i8 {
        self.bits
    }
}

impl cast::From<F1P7> for F1P7 {
    type Output = F1P7;

    fn cast(x: F1P7) -> Self::Output {
        x
    }
}

// NOTE handled above
// impl cast::From<F1P15> for F1P7 {}

impl cast::From<UF0P8> for F1P7 {
    type Output = F1P7;

    fn cast(x: UF0P8) -> Self::Output {
        F1P7 { bits: (x.bits >> 1) as i8 }
    }
}

impl cast::From<UF0P16> for F1P7 {
    type Output = F1P7;

    fn cast(x: UF0P16) -> Self::Output {
        F1P7 { bits: (x.bits >> 9) as i8 }
    }
}

impl cast::From<f32> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: f32) -> Self::Output {
        i8(x * (1 << 7) as f32).map(|b| F1P7 { bits: b })
    }
}

impl cast::From<f64> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: f64) -> Self::Output {
        i8(x * (1 << 7) as f64).map(|b| F1P7 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<F1P7> for F1P15 {}
// impl cast::From<F1P7> for F1P7 {}

impl cast::From<F1P7> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: F1P7) -> Self::Output {
        u16(x.bits).map(|b| UF0P16 { bits: b << 9 })
    }
}

impl cast::From<F1P7> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: F1P7) -> Self::Output {
        u8(x.bits).map(|b| UF0P8 { bits: b << 1 })
    }
}

impl cast::From<F1P7> for f32 {
    type Output = f32;

    fn cast(x: F1P7) -> Self::Output {
        f32(x.bits) / f32(1 << 7)
    }
}

impl cast::From<F1P7> for f64 {
    type Output = f64;

    fn cast(x: F1P7) -> Self::Output {
        f64(x.bits) / f64(1 << 7)
    }
}

impl fmt::Display for F1P7 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 10]))
    }
}

add!(F1P7);

div!(F1P7, 7, i16, i8);

mul!(F1P7, 7, i16, i8);

scale!(F1P7, i8);

shift!(F1P7(u8, u16, u32, u64, usize));

sub!(F1P7);

/// Range: `[-8388608.0, 8388608.0 - 2^-8]`. Precision: `2^-8`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct F24P8 {
    bits: i32,
}

impl F24P8 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        F24P8 { bits: (x * (1 << 8) as f64) as i32 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 20]) -> Str<'s> {
        const DIVISOR: u16 = 1 << 8;
        // index of b'.' in `buffer`
        const SPLIT: usize = 11;

        if self.bits == i32::MIN {
            const S: &'static [u8] = b"-8388608";

            buffer[..S.len()].copy_from_slice(S);

            return Str {
                       start: 0,
                       end: S.len(),
                       s: unsafe { mk_str(buffer.as_ptr(), S.len()) },
                   };
        }

        let mut int = (self.bits.abs() >> 8) as i32;
        if self.bits < 0 {
            int = -int
        }
        let mut start = int.numtoa(10, &mut buffer[..SPLIT]);
        if self.bits < 0 && int == 0 {
            start -= 1;
            buffer[start] = b'-';
        }

        let frac = u16(self.bits.abs() as u8);

        if frac == 0 {
            return Str {
                       start: start,
                       end: SPLIT,
                       s: unsafe {
                           mk_str(buffer.as_ptr().offset(start as isize),
                                  SPLIT - start)
                       },
                   };
        }

        buffer[SPLIT] = b'.';

        let end = unsafe {
            fmt16(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  frac,
                  DIVISOR)
        };

        Str {
            start: start,
            end: end + SPLIT + 1,
            s: unsafe {
                mk_str(buffer.as_ptr().offset(start as isize),
                       end + SPLIT + 1 - start)
            },
        }
    }

    /// Creates a `F24P8` from raw bits
    pub fn from_raw_bits(bits: i32) -> Self {
        F24P8 { bits: bits }
    }

    /// Turns `F24P8` into raw bits
    pub fn into_raw_bits(&self) -> i32 {
        self.bits
    }
}

// NOTE handled above
// impl cast::From<F16P16> for F24P8 {}
// impl cast::From<F1P15> for F24P8 {}

impl cast::From<F1P7> for F24P8 {
    type Output = F24P8;

    fn cast(x: F1P7) -> Self::Output {
        F24P8 { bits: i32(x.bits) << 1 }
    }
}

impl cast::From<F24P8> for F24P8 {
    type Output = F24P8;

    fn cast(x: F24P8) -> Self::Output {
        x
    }
}

impl cast::From<UF0P16> for F24P8 {
    type Output = F24P8;

    fn cast(x: UF0P16) -> Self::Output {
        F24P8 { bits: i32(x.bits >> 8) }
    }
}

impl cast::From<UF0P8> for F24P8 {
    type Output = F24P8;

    fn cast(x: UF0P8) -> Self::Output {
        F24P8 { bits: i32(x.bits) }
    }
}

impl cast::From<UF16P16> for F24P8 {
    type Output = F24P8;

    fn cast(x: UF16P16) -> Self::Output {
        F24P8 { bits: (x.bits >> 8) as i32 }
    }
}

impl cast::From<UF24P8> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i32(x.bits).map(|b| F24P8 { bits: b })
    }
}

impl cast::From<f32> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: f32) -> Self::Output {
        i32(x * (1 << 8) as f32).map(|b| F24P8 { bits: b })
    }
}

impl cast::From<f64> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: f64) -> Self::Output {
        i32(x * (1 << 8) as f64).map(|b| F24P8 { bits: b })
    }
}

impl cast::From<i8> for F24P8 {
    type Output = F24P8;

    fn cast(x: i8) -> Self::Output {
        F24P8(i16(x))
    }
}

impl cast::From<i16> for F24P8 {
    type Output = F24P8;

    fn cast(x: i16) -> Self::Output {
        F24P8 { bits: i32(x) << 8 }
    }
}

impl cast::From<i32> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: i32) -> Self::Output {
        i32(i64(x) << 8).map(|b| F24P8 { bits: b })
    }
}

impl cast::From<i64> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: i64) -> Self::Output {
        i32(x).and_then(F24P8)
    }
}

#[cfg(target_pointer_width = "32")]
impl cast::From<isize> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: isize) -> Self::Output {
        F24P8(i32(x))
    }
}

#[cfg(target_pointer_width = "64")]
impl cast::From<isize> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: isize) -> Self::Output {
        i32(x).and_then(F24P8)
    }
}

impl cast::From<u8> for F24P8 {
    type Output = F24P8;

    fn cast(x: u8) -> Self::Output {
        F24P8(i16(x))
    }
}

impl cast::From<u16> for F24P8 {
    type Output = F24P8;

    fn cast(x: u16) -> Self::Output {
        F24P8 { bits: i32(x) << 8 }
    }
}

impl cast::From<u32> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: u32) -> Self::Output {
        i32(x).map(|b| F24P8 { bits: b << 8 })
    }
}

impl cast::From<u64> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: u64) -> Self::Output {
        u32(x).and_then(F24P8)
    }
}

#[cfg(target_pointer_width = "32")]
impl cast::From<usize> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: usize) -> Self::Output {
        F24P8(u32(x))
    }
}

#[cfg(target_pointer_width = "64")]
impl cast::From<usize> for F24P8 {
    type Output = Result<F24P8, Error>;

    fn cast(x: usize) -> Self::Output {
        u32(x).and_then(F24P8)
    }
}

// NOTE handled above
// impl cast::From<F24P8> for F16P16 {}

impl cast::From<F24P8> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: F24P8) -> Self::Output {
        i16(x.bits << 7).map(|b| F1P15 { bits: b })
    }
}

impl cast::From<F24P8> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: F24P8) -> Self::Output {
        i8(x.bits >> 7).map(|b| F1P7 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<F24P8> for F24P8 {}

impl cast::From<F24P8> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u16(x.bits << 8).map(|b| UF0P16 { bits: b })
    }
}

impl cast::From<F24P8> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u8(x.bits).map(|b| UF0P8 { bits: b })
    }
}

impl cast::From<F24P8> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u32(x.bits << 8).map(|b| UF16P16 { bits: b })
    }
}

impl cast::From<F24P8> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u32(x.bits).map(|b| UF24P8 { bits: b })
    }
}

impl cast::From<F24P8> for f32 {
    type Output = f32;

    fn cast(x: F24P8) -> Self::Output {
        f32(x.bits) / f32(1 << 8)
    }
}

impl cast::From<F24P8> for f64 {
    type Output = f64;

    fn cast(x: F24P8) -> Self::Output {
        f64(x.bits) / f64(1 << 8)
    }
}

impl cast::From<F24P8> for i8 {
    type Output = Result<i8, Error>;

    fn cast(x: F24P8) -> Self::Output {
        i8(i32(x))
    }
}

impl cast::From<F24P8> for i16 {
    type Output = Result<i16, Error>;

    fn cast(x: F24P8) -> Self::Output {
        i16(i32(x))
    }
}

impl cast::From<F24P8> for i32 {
    type Output = i32;

    fn cast(x: F24P8) -> Self::Output {
        x.bits >> 8
    }
}

impl cast::From<F24P8> for i64 {
    type Output = i64;

    fn cast(x: F24P8) -> Self::Output {
        i64(i32(x))
    }
}

impl cast::From<F24P8> for isize {
    type Output = isize;

    fn cast(x: F24P8) -> Self::Output {
        isize(i32(x))
    }
}

impl cast::From<F24P8> for u8 {
    type Output = Result<u8, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u8(i32(x))
    }
}

impl cast::From<F24P8> for u16 {
    type Output = Result<u16, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u16(i32(x))
    }
}

impl cast::From<F24P8> for u32 {
    type Output = Result<u32, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u32(i32(x))
    }
}

impl cast::From<F24P8> for u64 {
    type Output = Result<u64, Error>;

    fn cast(x: F24P8) -> Self::Output {
        u64(i32(x))
    }
}

impl cast::From<F24P8> for usize {
    type Output = Result<usize, Error>;

    fn cast(x: F24P8) -> Self::Output {
        usize(i32(x))
    }
}

impl fmt::Display for F24P8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 20]))
    }
}

add!(F24P8);

add_int!(F24P8, 8, i16, i32);

div!(F24P8, 8, i64, i32);

mul_overflow!(F24P8, 8, i64, i32);

scale!(F24P8, i32);

shift!(F24P8(u8, u16, u32, u64, usize));

sub!(F24P8);

sub_int!(F24P8, 8, i16, i32);

/// Range: `[0.0, 1.0 - 2^-16]`. Precision: `2^-16`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UF0P16 {
    bits: u16,
}

impl UF0P16 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        UF0P16 { bits: (x * (1 << 16) as f64) as u16 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 18]) -> Str<'s> {
        const DIVISOR: u32 = 1 << 16;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 1;

        if self.bits == 0 {
            buffer[0] = b'0';

            return Str {
                       start: 0,
                       end: 1,
                       s: unsafe { mk_str(buffer.as_ptr(), 1) },
                   };
        }

        buffer[0] = b'0';
        buffer[SPLIT] = b'.';

        let i = unsafe {
            fmt32(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  self.bits as u32,
                  DIVISOR)
        };

        Str {
            start: 0,
            end: i + SPLIT + 1,
            s: unsafe { mk_str(buffer.as_ptr(), i + SPLIT + 1) },
        }
    }

    /// Creates a `UF0P16` from raw bits
    pub fn from_raw_bits(bits: u16) -> Self {
        UF0P16 { bits: bits }
    }

    /// Turns `UF0P16` into raw bits
    pub fn into_raw_bits(&self) -> u16 {
        self.bits
    }
}

impl cast::From<F1P15> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: F1P15) -> Self::Output {
        u16(x.bits).map(|b| UF0P16 { bits: b << 1 })
    }
}

// NOTE handled above
// impl cast::From<F1P7> for UF0P16 {}

impl cast::From<UF0P16> for UF0P16 {
    type Output = UF0P16;

    fn cast(x: UF0P16) -> Self::Output {
        x
    }
}

impl cast::From<UF0P8> for UF0P16 {
    type Output = UF0P16;

    fn cast(x: UF0P8) -> Self::Output {
        UF0P16 { bits: u16(x.bits) << 8 }
    }
}

impl cast::From<f32> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: f32) -> Self::Output {
        u16(x * (1 << 16) as f32).map(|b| UF0P16 { bits: b })
    }
}

impl cast::From<f64> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: f64) -> Self::Output {
        u16(x * (1 << 16) as f64).map(|b| UF0P16 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<UF0P16> for F1P15 {}
// impl cast::From<UF0P16> for F1P7 {}
// impl cast::From<UF0P16> for UF0P16 {}

impl cast::From<UF0P16> for UF0P8 {
    type Output = UF0P8;

    fn cast(x: UF0P16) -> Self::Output {
        UF0P8 { bits: (x.bits >> 8) as u8 }
    }
}

impl cast::From<UF0P16> for f32 {
    type Output = f32;

    fn cast(x: UF0P16) -> Self::Output {
        f32(x.bits) / f32(1 << 16)
    }
}

impl cast::From<UF0P16> for f64 {
    type Output = f64;

    fn cast(x: UF0P16) -> Self::Output {
        f64(x.bits) / f64(1 << 16)
    }
}

impl fmt::Display for UF0P16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0u8; 18]))
    }
}

add!(UF0P16);

div!(UF0P16, 16, u32, u16);

mul!(UF0P16, 16, u32, u16);

scale!(UF0P16, u16);

shift!(UF0P16(u8, u16, u32, u64, usize));

sub!(UF0P16);

/// Range: `[0.0, 1.0 - 2^-8]`. Precision: `2^-8`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UF0P8 {
    bits: u8,
}

impl UF0P8 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        UF0P8 { bits: (x * (1 << 8) as f64) as u8 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 10]) -> Str<'s> {
        const DIVISOR: u16 = 1 << 8;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 1;

        if self.bits == 0 {
            buffer[0] = b'0';

            return Str {
                       start: 0,
                       end: 1,
                       s: unsafe { mk_str(buffer.as_ptr(), 1) },
                   };
        }

        buffer[0] = b'0';
        buffer[SPLIT] = b'.';

        let i = unsafe {
            fmt16(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  self.bits as u16,
                  DIVISOR)
        };

        Str {
            start: 0,
            end: i + SPLIT + 1,
            s: unsafe { mk_str(buffer.as_ptr(), i + SPLIT + 1) },
        }
    }

    /// Creates a `UF0P8` from raw bits
    pub fn from_raw_bits(bits: u8) -> Self {
        UF0P8 { bits: bits }
    }

    /// Turns `UF0P8` into raw bits
    pub fn into_raw_bits(&self) -> u8 {
        self.bits
    }
}

impl cast::From<F1P15> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: F1P15) -> Self::Output {
        u16(x.bits).map(|b| UF0P8 { bits: (b >> 7) as u8 })
    }
}

// NOTE handled above
// impl cast::From<F1P7> for UF0P8 {}
// impl cast::From<UF0P16> for UF0P8 {}

impl cast::From<UF0P8> for UF0P8 {
    type Output = UF0P8;

    fn cast(x: UF0P8) -> Self::Output {
        x
    }
}

impl cast::From<f32> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: f32) -> Self::Output {
        u8(x * (1 << 8) as f32).map(|b| UF0P8 { bits: b })
    }
}

impl cast::From<f64> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: f64) -> Self::Output {
        u8(x * (1 << 8) as f64).map(|b| UF0P8 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<UF0P8> for F1P15 {}
// impl cast::From<UF0P8> for F1P7 {}
// impl cast::From<UF0P8> for UF0P16 {}
// impl cast::From<UF0P8> for UF0P8 {}

impl cast::From<UF0P8> for f32 {
    type Output = f32;

    fn cast(x: UF0P8) -> Self::Output {
        f32(x.bits) / f32(1 << 8)
    }
}

impl cast::From<UF0P8> for f64 {
    type Output = f64;

    fn cast(x: UF0P8) -> Self::Output {
        f64(x.bits) / f64(1 << 8)
    }
}

impl fmt::Display for UF0P8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 10]))
    }
}

add!(UF0P8);

div!(UF0P8, 8, u16, u8);

mul!(UF0P8, 8, u16, u8);

scale!(UF0P8, u8);

shift!(UF0P8(u8, u16, u32, u64, usize));

sub!(UF0P8);

/// Range: `[0.0, 65536.0 - 2^-16]`. Precision: `2^-16`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UF16P16 {
    bits: u32,
}

impl UF16P16 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        UF16P16 { bits: (x * (1 << 16) as f64) as u32 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 22]) -> Str<'s> {
        const DIVISOR: u32 = 1 << 16;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 5;

        let int = (self.bits >> 16) as u16;
        let start = int.numtoa(10, &mut buffer[..SPLIT]);

        let frac = u32(self.bits as u16);

        if frac == 0 {
            return Str {
                       start: start,
                       end: SPLIT,
                       s: unsafe {
                           mk_str(buffer.as_ptr().offset(start as isize),
                                  SPLIT - start)
                       },
                   };
        }

        buffer[SPLIT] = b'.';

        let end = unsafe {
            fmt32(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  frac,
                  DIVISOR)
        };

        Str {
            start: start,
            end: SPLIT + 1,
            s: unsafe {
                mk_str(buffer.as_ptr().offset(start as isize),
                       end + SPLIT + 1 - start)
            },
        }
    }

    /// Creates a `UF16P16` from raw bits
    pub fn from_raw_bits(bits: u32) -> Self {
        UF16P16 { bits: bits }
    }

    /// Turns `UF16P16` into raw bits
    pub fn into_raw_bits(&self) -> u32 {
        self.bits
    }
}

// NOTE handled above
// impl cast::From<F16P16> for UF16P16 {}

impl cast::From<F1P15> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: F1P15) -> Self::Output {
        u32(x.bits).map(|b| UF16P16 { bits: b << 1 })
    }
}

impl cast::From<F1P7> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: F1P7) -> Self::Output {
        u32(x.bits).map(|b| UF16P16 { bits: b << 9 })
    }
}

// NOTE handled above
// impl cast::From<F24P8> for UF16P16 {}

impl cast::From<UF0P16> for UF16P16 {
    type Output = UF16P16;

    fn cast(x: UF0P16) -> Self::Output {
        UF16P16 { bits: u32(x.bits) }
    }
}

impl cast::From<UF0P8> for UF16P16 {
    type Output = UF16P16;

    fn cast(x: UF0P8) -> Self::Output {
        UF16P16 { bits: u32(x.bits) << 8 }
    }
}

impl cast::From<UF16P16> for UF16P16 {
    type Output = UF16P16;

    fn cast(x: UF16P16) -> Self::Output {
        x
    }
}

impl cast::From<UF24P8> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        u32(u64(x.bits) << 8).map(|b| UF16P16 { bits: b })
    }
}

impl cast::From<f32> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: f32) -> Self::Output {
        u32(x * (1 << 16) as f32).map(|b| UF16P16 { bits: b })
    }
}

impl cast::From<f64> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: f64) -> Self::Output {
        u32(x * (1 << 16) as f64).map(|b| UF16P16 { bits: b })
    }
}

impl cast::From<i8> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: i8) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<i16> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: i16) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<i32> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: i32) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<i64> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: i64) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<isize> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: isize) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<u8> for UF16P16 {
    type Output = UF16P16;

    fn cast(x: u8) -> Self::Output {
        UF16P16(u16(x))
    }
}

impl cast::From<u16> for UF16P16 {
    type Output = UF16P16;

    fn cast(x: u16) -> Self::Output {
        UF16P16 { bits: u32(x) << 16 }
    }
}

impl cast::From<u32> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: u32) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<u64> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: u64) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

impl cast::From<usize> for UF16P16 {
    type Output = Result<UF16P16, Error>;

    fn cast(x: usize) -> Self::Output {
        u16(x).map(UF16P16)
    }
}

// NOTE handled above
// impl cast::From<UF16P16> for F16P16 {}

impl cast::From<UF16P16> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        i16(x.bits >> 1).map(|b| F1P15 { bits: b })
    }
}

impl cast::From<UF16P16> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        i8(x.bits >> 9).map(|b| F1P7 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<UF16P16> for F24P8 {}

impl cast::From<UF16P16> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        u16(x.bits).map(|b| UF0P16 { bits: b })
    }
}

impl cast::From<UF16P16> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        u8(x.bits >> 8).map(|b| UF0P8 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<UF16P16> for UF16P16 {}

impl cast::From<UF16P16> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: UF16P16) -> Self::Output {
        UF24P8 { bits: x.bits >> 8 }
    }
}

impl cast::From<UF16P16> for f32 {
    type Output = f32;

    fn cast(x: UF16P16) -> Self::Output {
        f32(x.bits) / f32(1 << 16)
    }
}

impl cast::From<UF16P16> for f64 {
    type Output = f64;

    fn cast(x: UF16P16) -> Self::Output {
        f64(x.bits) / f64(1 << 16)
    }
}

impl cast::From<UF16P16> for u8 {
    type Output = Result<u8, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        u8(u16(x))
    }
}

impl cast::From<UF16P16> for u16 {
    type Output = u16;

    fn cast(x: UF16P16) -> Self::Output {
        (x.bits >> 16) as u16
    }
}

impl cast::From<UF16P16> for u32 {
    type Output = u32;

    fn cast(x: UF16P16) -> Self::Output {
        (x.bits >> 16)
    }
}

impl cast::From<UF16P16> for u64 {
    type Output = u64;

    fn cast(x: UF16P16) -> Self::Output {
        u64(u32(x))
    }
}

impl cast::From<UF16P16> for usize {
    type Output = u64;

    fn cast(x: UF16P16) -> Self::Output {
        u64(u32(x))
    }
}

impl cast::From<UF16P16> for i8 {
    type Output = Result<i8, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        i8(u16(x))
    }
}

impl cast::From<UF16P16> for i16 {
    type Output = Result<i16, Error>;

    fn cast(x: UF16P16) -> Self::Output {
        i16(u16(x))
    }
}

impl cast::From<UF16P16> for i32 {
    type Output = i32;

    fn cast(x: UF16P16) -> Self::Output {
        i32(u16(x))
    }
}

impl cast::From<UF16P16> for i64 {
    type Output = i64;

    fn cast(x: UF16P16) -> Self::Output {
        i64(u16(x))
    }
}

impl cast::From<UF16P16> for isize {
    type Output = isize;

    fn cast(x: UF16P16) -> Self::Output {
        isize(u16(x))
    }
}

impl fmt::Display for UF16P16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 22]))
    }
}

add!(UF16P16);

add_int!(UF16P16, 16, u16, u32);

div!(UF16P16, 16, u64, u32);

mul!(UF16P16, 16, u64, u32);

scale!(UF16P16, u32);

shift!(UF16P16(u8, u16, u32, u64, usize));

sub!(UF16P16);

sub_int!(UF16P16, 16, u16, u32);

/// Range: `[0.0, 16777216.0 - 2^-8]`. Precision: `2^-8`
#[derive(Clone, Copy, Debug)]
pub struct UF24P8 {
    bits: u32,
}

impl UF24P8 {
    /// Creates a new fixed point value
    #[cfg(feature = "const-fn")]
    pub const fn new(x: f64) -> Self {
        UF24P8 { bits: (x * (1 << 8) as f64) as u32 }
    }

    /// Formats the value into `buffer`
    pub fn fmt<'s>(&self, buffer: &'s mut [u8; 19]) -> Str<'s> {
        const DIVISOR: u16 = 1 << 8;
        // Byte index of b'.' in `buffer`
        const SPLIT: usize = 10;

        let int = self.bits >> 8;
        let start = int.numtoa(10, &mut buffer[..SPLIT]);

        let frac = u16(self.bits as u8);

        if frac == 0 {
            return Str {
                       start: start,
                       end: SPLIT,
                       s: unsafe {
                           mk_str(buffer.as_ptr().offset(start as isize),
                                  SPLIT - start)
                       },
                   };
        }

        buffer[SPLIT] = b'.';

        let end = unsafe {
            fmt16(buffer.as_mut_ptr().offset(SPLIT as isize + 1),
                  frac,
                  DIVISOR)
        };

        Str {
            start: start,
            end: end + SPLIT + 1,
            s: unsafe {
                mk_str(buffer.as_ptr().offset(start as isize),
                       end + SPLIT + 1 - start)
            },
        }
    }

    /// Creates a `UF24P8` from raw bits
    pub fn from_raw_bits(bits: u32) -> Self {
        UF24P8 { bits: bits }
    }

    /// Turns `UF24P8` into raw bits
    pub fn into_raw_bits(&self) -> u32 {
        self.bits
    }
}

// NOTE handled above
// impl cast::From<F16P16> for UF24P8 {}

impl cast::From<F1P15> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: F1P15) -> Self::Output {
        u32(x.bits).map(|b| UF24P8 { bits: b >> 7 })
    }
}

impl cast::From<F1P7> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: F1P7) -> Self::Output {
        u32(x.bits).map(|b| UF24P8 { bits: b << 1 })
    }
}

// NOTE handled above
// impl cast::From<F24P8> for UF24P8 {}

impl cast::From<UF0P16> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: UF0P16) -> Self::Output {
        UF24P8 { bits: u32(x.bits) >> 8 }
    }
}

impl cast::From<UF0P8> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: UF0P8) -> Self::Output {
        UF24P8 { bits: u32(x.bits) }
    }
}

// NOTE handled above
// impl cast::From<UF16P16> for UF24P8 {}

impl cast::From<UF24P8> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: UF24P8) -> Self::Output {
        x
    }
}

impl cast::From<f32> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: f32) -> Self::Output {
        u32(x * (1 << 8) as f32).map(|b| UF24P8 { bits: b })
    }
}

impl cast::From<f64> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: f64) -> Self::Output {
        u32(x * (1 << 8) as f64).map(|b| UF24P8 { bits: b })
    }
}

impl cast::From<i8> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: i8) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

impl cast::From<i16> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: i16) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

impl cast::From<i32> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: i32) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

impl cast::From<i64> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: i64) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

impl cast::From<isize> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: isize) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

impl cast::From<u8> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: u8) -> Self::Output {
        UF24P8 { bits: u32(x) << 8 }
    }
}

impl cast::From<u16> for UF24P8 {
    type Output = UF24P8;

    fn cast(x: u16) -> Self::Output {
        UF24P8 { bits: u32(x) << 8 }
    }
}

impl cast::From<u32> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: u32) -> Self::Output {
        u32(u64(x) << 8).map(|b| UF24P8 { bits: b })
    }
}

impl cast::From<u64> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: u64) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

#[cfg(target_pointer_width = "32")]
impl cast::From<usize> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: usize) -> Self::Output {
        UF24P8(u32(x))
    }
}

#[cfg(target_pointer_width = "64")]
impl cast::From<usize> for UF24P8 {
    type Output = Result<UF24P8, Error>;

    fn cast(x: usize) -> Self::Output {
        u32(x).and_then(UF24P8)
    }
}

// NOTE handled above
// impl cast::From<UF24P8> for F16P16 {}

impl cast::From<UF24P8> for F1P15 {
    type Output = Result<F1P15, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i16(x.bits).map(|b| F1P15 { bits: b << 7 })
    }
}

impl cast::From<UF24P8> for F1P7 {
    type Output = Result<F1P7, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i8(x.bits).map(|b| F1P7 { bits: b >> 1 })
    }
}

// NOTE handled above
// impl cast::From<UF24P8> for F24P8 {}

impl cast::From<UF24P8> for UF0P16 {
    type Output = Result<UF0P16, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        u16(x.bits).map(|b| UF0P16 { bits: b << 8 })
    }
}

impl cast::From<UF24P8> for UF0P8 {
    type Output = Result<UF0P8, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        u8(x.bits).map(|b| UF0P8 { bits: b })
    }
}

// NOTE handled above
// impl cast::From<UF24P8> for UF16P16 {}
// impl cast::From<UF24P8> for UF24P8 {}

impl cast::From<UF24P8> for f32 {
    type Output = f32;

    fn cast(x: UF24P8) -> Self::Output {
        f32(x.bits) / f32(1 << 8)
    }
}

impl cast::From<UF24P8> for f64 {
    type Output = f64;

    fn cast(x: UF24P8) -> Self::Output {
        f64(x.bits) / f64(1 << 8)
    }
}

impl cast::From<UF24P8> for i8 {
    type Output = Result<i8, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i8(u32(x))
    }
}

impl cast::From<UF24P8> for i16 {
    type Output = Result<i16, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i16(u32(x))
    }
}

impl cast::From<UF24P8> for i32 {
    type Output = Result<i32, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        i32(u32(x))
    }
}

impl cast::From<UF24P8> for i64 {
    type Output = i64;

    fn cast(x: UF24P8) -> Self::Output {
        i64(u32(x))
    }
}

#[cfg(target_pointer_width = "32")]
impl cast::From<UF24P8> for isize {
    type Output = Result<isize, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        isize(u32(x))
    }
}

#[cfg(target_pointer_width = "64")]
impl cast::From<UF24P8> for isize {
    type Output = isize;

    fn cast(x: UF24P8) -> Self::Output {
        isize(u32(x))
    }
}

impl cast::From<UF24P8> for u8 {
    type Output = Result<u8, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        u8(u32(x))
    }
}

impl cast::From<UF24P8> for u16 {
    type Output = Result<u16, Error>;

    fn cast(x: UF24P8) -> Self::Output {
        u16(u32(x))
    }
}

impl cast::From<UF24P8> for u32 {
    type Output = u32;

    fn cast(x: UF24P8) -> Self::Output {
        x.bits >> 8
    }
}

impl cast::From<UF24P8> for u64 {
    type Output = u64;

    fn cast(x: UF24P8) -> Self::Output {
        u64(u32(x))
    }
}

impl cast::From<UF24P8> for usize {
    type Output = usize;

    fn cast(x: UF24P8) -> Self::Output {
        usize(u32(x))
    }
}

impl fmt::Display for UF24P8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&*self.fmt(&mut [0; 19]))
    }
}

add!(UF24P8);

add_int!(UF24P8, 8, u16, u32);

div!(UF24P8, 8, u64, u32);

mul_overflow!(UF24P8, 8, u64, u32);

scale!(UF24P8, u32);

shift!(UF24P8(u8, u16, u32, u64, usize));

sub!(UF24P8);

sub_int!(UF24P8, 8, u16, u32);

/// Formatted fixed point number
pub struct Str<'a> {
    end: usize,
    s: &'a str,
    start: usize,
}

impl<'a> Str<'a> {
    /// End byte offset of the formatted string wrt to the original buffer
    ///
    /// It holds that `&buffer[self.start()..self.end()] == self.deref()`
    pub fn end(&self) -> usize {
        self.end
    }

    /// Start byte offset of the formatted string wrt to the original buffer
    ///
    /// It holds that `&buffer[self.start()..self.end()] == self.deref()`
    pub fn start(&self) -> usize {
        self.start
    }
}

impl<'a> ops::Deref for Str<'a> {
    type Target = str;

    fn deref(&self) -> &str {
        self.s
    }
}

unsafe fn fmt16(mut buffer: *mut u8, mut dividend: u16, divisor: u16) -> usize {
    let mut i = 0;
    loop {
        dividend *= 10;

        *buffer = *DIGITS.as_ptr().offset(isize(dividend / divisor));
        buffer = buffer.offset(1);
        i += 1;

        dividend %= divisor;

        if dividend == 0 {
            return i;
        }
    }
}

unsafe fn fmt32(mut buffer: *mut u8, mut dividend: u32, divisor: u32) -> usize {
    let mut i = 0;
    loop {
        dividend *= 10;

        *buffer = *DIGITS.as_ptr().offset((dividend / divisor) as isize);
        buffer = buffer.offset(1);
        i += 1;

        dividend %= divisor;

        if dividend == 0 {
            return i;
        }
    }
}

unsafe fn mk_str<'a>(ptr: *const u8, len: usize) -> &'a str {
    str::from_utf8_unchecked(slice::from_raw_parts(ptr, len))
}

macro_rules! fns {
    ($($ty:ident),+) => {
        $(
            /// Checked cast function
            #[inline]
            #[allow(non_snake_case)]
            pub fn $ty<T>(x: T) -> <$ty as cast::From<T>>::Output
                where $ty: cast::From<T>
            {
                <$ty as cast::From<T>>::cast(x)
            }
        )+
    }
}

fns!(F16P16, F1P15, F1P7, F24P8, UF0P16, UF0P8, UF16P16, UF24P8);
