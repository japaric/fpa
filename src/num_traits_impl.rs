use core::marker::PhantomData;
use core::ops;

use typenum::Unsigned;

use num_traits::{self, sign};
use num_traits::identities::{One, Zero};

use cast;

use Q;

#[derive(PartialEq, Debug)]
pub struct ParseFixedError;

impl<BITS, FRAC> Zero for Q<BITS, FRAC>
where
    BITS: Zero + PartialEq,
    FRAC: Unsigned,
    Self: ops::Add<Self, Output = Self>
{
    fn zero() -> Self {
        Q { bits: BITS::zero(), _marker: PhantomData }
    }

    fn is_zero(&self) -> bool {
        self.bits == BITS::zero()
    }
}

impl<BITS, FRAC> One for Q<BITS, FRAC>
where
    BITS: One + ops::Shl<u8, Output = BITS> + PartialEq,
    FRAC: Unsigned,
    Self: ops::Mul<Self, Output = Self>
{
    fn one() -> Self {
        Q { bits: BITS::one() << FRAC::to_u8(), _marker: PhantomData }
    }

    fn is_one(&self) -> bool {
        self.bits == BITS::one() << FRAC::to_u8()
    }
}

impl<BITS, FRAC> num_traits::Num for Q<BITS, FRAC>
where
    Self: PartialEq + Zero + One + num_traits::NumOps + cast::From<f64, Output = Result<Self, cast::Error>>
{
    type FromStrRadixErr = ParseFixedError;

    fn from_str_radix(
        str: &str,
        radix: u32
    ) -> Result<Self, Self::FromStrRadixErr> {
        use cast::From;
        let f = f64::from_str_radix(str, radix).map_err(|_| ParseFixedError);
        f.and_then(|f| Self::cast(f).map_err(|_| ParseFixedError))
    }
}

impl<BITS, FRAC> sign::Signed for Q<BITS, FRAC>
where
    BITS: sign::Signed + ops::Shl<u8, Output = BITS>,
    FRAC: Unsigned,
    Self: num_traits::Num + ops::Neg<Output = Self>
{
    fn abs(&self) -> Self {
        Q { bits: self.bits.abs(), _marker: PhantomData }
    }

    fn abs_sub(&self, other: &Self) -> Self {
        // if *self <= *other { 0 } else { *self - *other }
        Q { bits: self.bits.abs_sub(&other.bits), _marker: PhantomData }
    }

    /// Returns the sign of the number.
    ///
    /// - `0` if the number is zero
    /// - `1` if the number is positive
    /// - `-1` if the number is negative
    fn signum(&self) -> Self {
        Q { bits: self.bits.signum() << FRAC::to_u8(), _marker: PhantomData }
    }

    fn is_positive(&self) -> bool {
        self.bits.is_positive()
    }

    fn is_negative(&self) -> bool {
        self.bits.is_negative()
    }
}

#[cfg(test)]
mod tests {
    macro_rules! test_types {
        (small: $head:ident, $($tail:ident),+) => {
            test_types!(small: $head);
            test_types!(small: $($tail),+);
        };
        (small: $ty:ident) => {
            #[allow(non_snake_case)]
            mod $ty {
                use ::*;

                #[test]
                fn zero() {
                    use num_traits::Zero;

                    assert_eq!($ty::zero(), $ty(0i8).unwrap());
                    assert_eq!($ty::zero().is_zero(), true);
                }

                #[test]
                #[should_panic]
                fn one() {
                    use num_traits::One;

                    assert_eq!($ty::one(), $ty(1i8).unwrap());
                    assert_eq!($ty::one().is_one(), true);
                }

                #[test]
                fn abs() {
                    use num_traits::Signed;

                    let pos_0 = $ty(0.0f32).unwrap();
                    let neg_0 = $ty(-0.0f32).unwrap();
                    let pos = $ty(0.1f32).unwrap();
                    let neg = $ty(-0.1f32).unwrap();

                    assert_eq!(pos_0.abs(), pos_0);
                    assert_eq!(neg_0.abs(), pos_0);
                    assert_eq!(neg.abs(), pos);
                    assert_eq!(pos.abs(), pos);
                }

                #[test]
                fn abs_sub() {
                    use num_traits::Signed;

                    let pos_0 = $ty(0.0f32).unwrap();
                    let neg_0 = $ty(-0.0f32).unwrap();
                    let pos = $ty(0.1f32).unwrap();
                    let neg = $ty(-0.1f32).unwrap();

                    assert_eq!(pos.abs_sub(&pos_0), pos);
                    assert_eq!(pos_0.abs_sub(&pos), pos_0);

                    assert_eq!(neg.abs_sub(&neg_0), pos_0);
                    assert_eq!(neg_0.abs_sub(&neg), pos);
                }

                #[test]
                fn is_positive() {
                    use num_traits::Signed;

                    assert_eq!($ty(0.0f32).unwrap().is_positive(), false);
                    assert_eq!($ty(-0.0f32).unwrap().is_positive(), false);
                    assert_eq!($ty(0.1f32).unwrap().is_positive(), true);
                    assert_eq!($ty(-0.1f32).unwrap().is_positive(), false);
                }

                #[test]
                fn is_negative() {
                    use num_traits::Signed;

                    assert_eq!($ty(0.0f32).unwrap().is_negative(), false);
                    assert_eq!($ty(-0.0f32).unwrap().is_negative(), false);
                    assert_eq!($ty(0.1f32).unwrap().is_negative(), false);
                    assert_eq!($ty(-0.1f32).unwrap().is_negative(), true);
                }
            }
        };
        (medium: $head:ident, $($tail:ident),+) => {
            test_types!(medium: $head);
            test_types!(medium: $($tail),+);
        };
        (medium: $ty:ident) => {
            #[allow(non_snake_case)]
            mod $ty {
                use ::*;

                #[test]
                fn zero() {
                    use num_traits::Zero;

                    assert_eq!($ty::zero(), $ty(0i8).unwrap());
                    assert_eq!($ty::zero().is_zero(), true);
                }

                #[test]
                fn one() {
                    use num_traits::One;

                    assert_eq!($ty::one(), $ty(1i8).unwrap());
                    assert_eq!($ty::one().is_one(), true);
                }

                #[test]
                fn from_str_radix() {
                    use num_traits::Num;

                    assert_eq!($ty::from_str_radix("1.0", 10), Ok($ty(1i8).unwrap()));
                }

                #[test]
                fn abs() {
                    use num_traits::Signed;

                    assert_eq!($ty(1i8).unwrap().abs(), $ty(1i8).unwrap());
                    assert_eq!($ty(-1i8).unwrap().abs(), $ty(1i8).unwrap());
                }

                #[test]
                fn abs_sub() {
                    use num_traits::Signed;

                    assert_eq!($ty(1i8).unwrap().abs_sub(&($ty(0i8).unwrap())), $ty(1i8).unwrap());
                    assert_eq!($ty(0i8).unwrap().abs_sub(&($ty(1i8).unwrap())), $ty(0i8).unwrap());

                    assert_eq!($ty(-1i8).unwrap().abs_sub(&($ty(-0i8).unwrap())), $ty(0i8).unwrap());
                    assert_eq!($ty(-0i8).unwrap().abs_sub(&($ty(-1i8).unwrap())), $ty(1i8).unwrap());
                }

                #[test]
                fn signum() {
                    use num_traits::Signed;

                    assert_eq!($ty(1i8).unwrap().signum(), $ty(1i8).unwrap());
                    assert_eq!($ty(-1i8).unwrap().signum(), $ty(-1i8).unwrap());
                    assert_eq!($ty(0i8).unwrap().signum(), $ty(0i8).unwrap());
                    assert_eq!($ty(-0i8).unwrap().signum(), $ty(0i8).unwrap());
                }

                #[test]
                fn is_positive() {
                    use num_traits::Signed;

                    assert_eq!($ty(1i8).unwrap().is_positive(), true);
                    assert_eq!($ty(-1i8).unwrap().is_positive(), false);
                    assert_eq!($ty(0i8).unwrap().is_positive(), false);
                    assert_eq!($ty(-0i8).unwrap().is_positive(), false);
                }

                #[test]
                fn is_negative() {
                    use num_traits::Signed;

                    assert_eq!($ty(1i8).unwrap().is_negative(), false);
                    assert_eq!($ty(-1i8).unwrap().is_negative(), true);
                    assert_eq!($ty(0i8).unwrap().is_negative(), false);
                    assert_eq!($ty(-0i8).unwrap().is_negative(), false);
                }
            }
        };
        (large: $head:ident, $($tail:ident),+) => {
            test_types!(large: $head);
            test_types!(large: $($tail),+);
        };
        (large: $ty:ident) => {
            #[allow(non_snake_case)]
            mod $ty {
                use ::*;

                #[test]
                fn zero() {
                    use num_traits::Zero;

                    assert_eq!($ty::zero(), $ty(0i8));
                    assert_eq!($ty::zero().is_zero(), true);
                }

                #[test]
                fn one() {
                    use num_traits::One;

                    assert_eq!($ty::one(), $ty(1i8));
                    assert_eq!($ty::one().is_one(), true);
                }

                #[test]
                fn from_str_radix() {
                    use num_traits::Num;

                    assert_eq!($ty::from_str_radix("1.0", 10), Ok($ty(1i8)));
                }

                #[test]
                fn abs() {
                    use num_traits::Signed;

                    assert_eq!($ty(42i8).abs(), $ty(42i8));
                    assert_eq!($ty(-42i8).abs(), $ty(42i8));
                }

                #[test]
                fn abs_sub() {
                    use num_traits::Signed;

                    assert_eq!($ty(42i8).abs_sub(&$ty(10i8)), $ty(32i8));
                    assert_eq!($ty(10i8).abs_sub(&$ty(42i8)), $ty(0i8));

                    assert_eq!($ty(-42i8).abs_sub(&$ty(-10i8)), $ty(0i8));
                    assert_eq!($ty(-10i8).abs_sub(&$ty(-42i8)), $ty(32i8));
                }

                #[test]
                fn signum() {
                    use num_traits::Signed;

                    assert_eq!($ty(42i8).signum(), $ty(1i8));
                    assert_eq!($ty(-42i8).signum(), $ty(-1i8));
                    assert_eq!($ty(0i8).signum(), $ty(0i8));
                    assert_eq!($ty(-0i8).signum(), $ty(0i8));
                }

                #[test]
                fn is_positive() {
                    use num_traits::Signed;

                    assert_eq!($ty(42i8).is_positive(), true);
                    assert_eq!($ty(-42i8).is_positive(), false);
                    assert_eq!($ty(0i8).is_positive(), false);
                    assert_eq!($ty(-0i8).is_positive(), false);
                }

                #[test]
                fn is_negative() {
                    use num_traits::Signed;

                    assert_eq!($ty(42i8).is_negative(), false);
                    assert_eq!($ty(-42i8).is_negative(), true);
                    assert_eq!($ty(0i8).is_negative(), false);
                    assert_eq!($ty(-0i8).is_negative(), false);
                }
            }
        };
    }

    // Types with an integer value range of 0..0:
    test_types!(small:
        I1F7, I1F15, I1F31
    );

    // Types with an integer value range smaller than that of i8:
    test_types!(medium:
        I2F6, I2F14, I2F30,
        I3F5, I3F13, I3F29,
        I4F4, I4F12, I4F28,
        I5F3, I5F11, I5F27,
        I6F2, I6F10, I6F26,
        I7F1, I7F9, I7F25
    );

    // Types with an integer value range larger than that of i8:
    test_types!(large:
        I8F8, I8F24,
        I9F7, I9F23,
        I10F6, I10F22,
        I11F5, I11F21,
        I12F4, I12F20,
        I13F3, I13F19,
        I14F2, I14F18,
        I15F1, I15F17,
        I16F16,
        I17F15,
        I18F14,
        I19F13,
        I20F12,
        I21F11,
        I22F10,
        I23F9,
        I24F8,
        I25F7,
        I26F6,
        I27F5,
        I28F4,
        I29F3,
        I30F2,
        I31F1
    );
}
