#![feature(rustc_attrs)]
#![feature(core_intrinsics)]
#![feature(unchecked_math)]
#![feature(const_trait_impl)]
#![feature(const_mut_refs)]

//! Similar to [`std::num`] `NonZero` types.

//! Additional functionality for numerics.
//! 
//! This crate provides some extra types that are useful when doing numerical work. See the
//! individual documentation for each piece for more information.

//! ## Features
//! 
//! - `ext`: Additional functionality beyond mimicking [`std::num`].

use std::fmt;
use std::ops::{BitOr,BitOrAssign};
use std::str::FromStr;
use std::intrinsics;

macro_rules! impl_non_negative_fmt {
    ( ( $( $Trait: ident ),+ ) for $Ty: ident ) => {
        $(
            impl fmt::$Trait for $Ty {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.get().fmt(f)
                }
            }
        )+
    }
}

macro_rules! nonnegative_integers {
    ( $( $Ty: ident($Int: ty), $end: literal; )+ ) => {
        $(
            /// A signed integer that is known not to be negative.
            ///
            /// This enables some memory layout optimization.
            #[doc = concat!("For example, `Option<", stringify!($Ty), ">` is the same size as `", stringify!($Int), "`:")]
            ///
            /// ```rust
            /// use std::mem::size_of;
            #[doc = concat!("assert_eq!(size_of::<Option<non_negative::", stringify!($Ty), ">>(), size_of::<", stringify!($Int), ">());")]
            /// ```
            #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
            #[repr(transparent)]
            #[rustc_layout_scalar_valid_range_start(0)]
            #[rustc_layout_scalar_valid_range_end($end)]
            #[rustc_diagnostic_item = stringify!($Ty)]
            pub struct $Ty($Int);

            impl $Ty {
                /// Creates a non-negative without checking whether the value is non-negative.
                /// This results in undefined behaviour if the value is negative.
                ///
                /// # Safety
                ///
                /// The value must not be negative.
                #[must_use]
                #[inline]
                pub const unsafe fn new_unchecked(n: $Int) -> Self {
                    Self(n)
                }

                /// Creates a non-negative if the given value is not negative.
                #[must_use]
                #[inline]
                pub const fn new(n: $Int) -> Option<Self> {
                    if n >= 0 {
                        // SAFETY: we just checked that there's no `0`
                        Some(unsafe { Self(n) })
                    } else {
                        None
                    }
                }

                /// Returns the value as a primitive type.
                #[inline]
                pub const fn get(self) -> $Int {
                    self.0
                }

            }

            impl const From<$Ty> for $Int {
                #[doc = concat!("Converts a `", stringify!($Ty), "` into an `", stringify!($Int), "`")]
                #[inline]
                fn from(nonnegative: $Ty) -> Self {
                    nonnegative.0
                }
            }

            impl const BitOr for $Ty {
                type Output = Self;
                #[inline]
                fn bitor(self, rhs: Self) -> Self::Output {
                    // SAFETY: since `self` and `rhs` are both nonnegative, the
                    // result of the bitwise-or will be nonnegative.
                    unsafe { $Ty::new_unchecked(self.get() | rhs.get()) }
                }
            }

            impl const BitOr<$Int> for $Ty {
                type Output = Self;
                #[inline]
                fn bitor(self, rhs: $Int) -> Self::Output {
                    // SAFETY: since `self` is nonnegative, the result of the
                    // bitwise-or will be nonnegative regardless of the value of
                    // `rhs`.
                    unsafe { $Ty::new_unchecked(self.get() | rhs) }
                }
            }

            impl const BitOr<$Ty> for $Int {
                type Output = $Ty;
                #[inline]
                fn bitor(self, rhs: $Ty) -> Self::Output {
                    // SAFETY: since `rhs` is nonnegative, the result of the
                    // bitwise-or will be nonnegative regardless of the value of
                    // `self`.
                    unsafe { $Ty::new_unchecked(self | rhs.get()) }
                }
            }

            impl const BitOrAssign for $Ty {
                #[inline]
                fn bitor_assign(&mut self, rhs: Self) {
                    *self = *self | rhs;
                }
            }

            impl const BitOrAssign<$Int> for $Ty {
                #[inline]
                fn bitor_assign(&mut self, rhs: $Int) {
                    *self = *self | rhs;
                }
            }

            impl_non_negative_fmt! {
                (Debug, Display, Binary, Octal, LowerHex, UpperHex) for $Ty
            }
        )+
    }
}

nonnegative_integers!{
    NonNegativeI8(i8), 0x80;
    NonNegativeI16(i16), 0x8000;
    NonNegativeI32(i32), 0x8000_0000;
    NonNegativeI64(i64), 0x8000_0000_0000_0000;
    NonNegativeI128(i128), 0x8000_0000_0000_0000_0000_0000_0000_0000;
    // TODO: Consider 32 bit cases
    NonNegativeIsize(isize), 0x8000_0000_0000_0000;
}
use std::num;
use std::num::IntErrorKind;
#[derive(Debug)]
pub struct ParseIntError {
    pub kind: IntErrorKind
}
impl From<IntErrorKind> for ParseIntError {
    fn from(kind: IntErrorKind) -> Self {
        Self { kind }
    }
}
impl From<num::ParseIntError> for ParseIntError {
    fn from(other: num::ParseIntError) -> Self {
        Self {
            kind: other.kind().clone()
        }
    }
}
impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            IntErrorKind::Empty => write!(f, "cannot parse integer from empty string"),
            IntErrorKind::InvalidDigit => write!(f, "invalid digit found in string"),
            IntErrorKind::PosOverflow => write!(f, "number too large to fit in target type"),
            IntErrorKind::NegOverflow => write!(f, "number too small to fit in target type"),
            IntErrorKind::Zero => write!(f, "number would be zero for non-zero type"),
            _ => unreachable!()
        }
    }
}
impl std::error::Error for ParseIntError {}

macro_rules! from_str_radix_nzint_impl {
    ($( $Ty: ident($Int: ty); )+) => {
        $(
            impl FromStr for $Ty {
                type Err = ParseIntError;
                fn from_str(src: &str) -> Result<Self, Self::Err> {
                    // In std it does
                    // ```
                    // .ok_or(ParseIntError {
                    //     kind: IntErrorKind::Zero
                    // })
                    // ```
                    // Since we cannot construct `ParseIntError` we use a custom type.
                    Self::new(<$Int>::from_str_radix(src, 10)?)
                        .ok_or(ParseIntError { kind: IntErrorKind::Zero })
                }
            }
        )+
    }
}
from_str_radix_nzint_impl! { 
    NonNegativeI8(i8);
    NonNegativeI16(i16);
    NonNegativeI32(i32);
    NonNegativeI64(i64);
    NonNegativeI128(i128);
    NonNegativeIsize(isize);
}

macro_rules! non_negative_leading_trailing_zeros {
    ( $( $Ty: ident($Uint: ty), $LeadingTestExpr:expr;)+ ) => {
        $(
            impl $Ty {
                /// Returns the number of leading zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                #[doc = concat!("let n = non_negative::", stringify!($Ty), "::new(", stringify!($LeadingTestExpr), ").unwrap();")]
                ///
                /// assert_eq!(n.leading_zeros(), 1);
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn leading_zeros(self) -> u32 {
                    intrinsics::ctlz(self.0 as $Uint) as u32
                }

                /// Returns the number of trailing zeros in the binary representation
                /// of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                #[doc = concat!("let n = non_negative::", stringify!($Ty), "::new(0b0101000).unwrap();")]
                ///
                /// assert_eq!(n.trailing_zeros(), 3);
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn trailing_zeros(self) -> u32 {
                    intrinsics::cttz(self.0 as $Uint) as u32
                }

            }
        )+
    }
}

non_negative_leading_trailing_zeros! {
    NonNegativeI8(i8), i8::MAX;
    NonNegativeI16(i16), i16::MAX;
    NonNegativeI32(i32), i32::MAX;
    NonNegativeI64(i64), i64::MAX;
    NonNegativeI128(i128), i128::MAX;
    NonNegativeIsize(isize), isize::MAX;
}

// A bunch of methods.
macro_rules! non_negative_operations {
    ( $( $Ty: ident($Int: ty); )+ ) => {
        $(
            impl $Ty {
                /// Multiplies two non-negative integers together.
                /// Checks for overflow and returns [`None`] on overflow.
                /// As a consequence, the result cannot wrap to negative.
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                /// # fn main() { test().unwrap(); }
                /// # fn test() -> Option<()> {
                #[doc = concat!("let two = ", stringify!($Ty), "::new(2)?;")]
                #[doc = concat!("let four = ", stringify!($Ty), "::new(4)?;")]
                #[doc = concat!("let max = ", stringify!($Ty), "::new(",
                                stringify!($Int), "::MAX)?;")]
                ///
                /// assert_eq!(Some(four), two.checked_mul(two));
                /// assert_eq!(None, max.checked_mul(two));
                /// # Some(())
                /// # }
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn checked_mul(self, other: $Ty) -> Option<$Ty> {
                    if let Some(result) = self.get().checked_mul(other.get()) {
                        // SAFETY: checked_mul returns None on overflow
                        // and `other` is also non-negative
                        // so the result cannot be negative.
                        Some(unsafe { $Ty::new_unchecked(result) })
                    } else {
                        None
                    }
                }

                /// Multiplies two non-negative integers together.
                #[doc = concat!("Return [`", stringify!($Int), "::MAX`] on overflow.")]
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                /// # fn main() { test().unwrap(); }
                /// # fn test() -> Option<()> {
                #[doc = concat!("let two = ", stringify!($Ty), "::new(2)?;")]
                #[doc = concat!("let four = ", stringify!($Ty), "::new(4)?;")]
                #[doc = concat!("let max = ", stringify!($Ty), "::new(",
                                stringify!($Int), "::MAX)?;")]
                ///
                /// assert_eq!(four, two.saturating_mul(two));
                /// assert_eq!(max, four.saturating_mul(max));
                /// # Some(())
                /// # }
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn saturating_mul(self, other: $Ty) -> $Ty {
                    // SAFETY: saturating_mul returns u*::MAX on overflow
                    // and `0` on underflow.
                    match self.get().saturating_mul(other.get()) {
                        x @ 0.. => unsafe { $Ty::new_unchecked(x) },
                        _ => unsafe { $Ty::new_unchecked(0) }
                    }
                    
                }

                /// Multiplies two non-negative integers together,
                /// assuming overflow cannot occur.
                /// Overflow is unchecked, and it is undefined behaviour to overflow
                /// *even if the result would wrap to a non-negative value*.
                /// The behaviour is undefined as soon as
                #[doc = concat!(
                    "`self * rhs > ", stringify!($Int), "::MAX`, ",
                    "or `self * rhs < ", stringify!($Int), "::MIN`."
                )]
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                /// # fn main() { test().unwrap(); }
                /// # fn test() -> Option<()> {
                #[doc = concat!("let two = ", stringify!($Ty), "::new(2)?;")]
                #[doc = concat!("let four = ", stringify!($Ty), "::new(4)?;")]
                ///
                /// assert_eq!(four, unsafe { two.unchecked_mul(two) });
                /// # Some(())
                /// # }
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub unsafe fn unchecked_mul(self, other: $Ty) -> $Ty {
                    // SAFETY: The caller ensures there is no overflow.
                    unsafe { $Ty::new_unchecked(self.get().unchecked_mul(other.get())) }
                }

                /// Raises non-negative value to an integer power.
                /// Checks for overflow and returns [`None`] on overflow.
                /// As a consequence, the result cannot wrap to negative.
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                /// # fn main() { test().unwrap(); }
                /// # fn test() -> Option<()> {
                #[doc = concat!("let three = ", stringify!($Ty), "::new(3)?;")]
                #[doc = concat!("let twenty_seven = ", stringify!($Ty), "::new(27)?;")]
                #[doc = concat!("let half_max = ", stringify!($Ty), "::new(",
                                stringify!($Int), "::MAX / 2)?;")]
                ///
                /// assert_eq!(Some(twenty_seven), three.checked_pow(3));
                /// assert_eq!(None, half_max.checked_pow(3));
                /// # Some(())
                /// # }
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn checked_pow(self, other: u32) -> Option<$Ty> {
                    if let Some(result) = self.get().checked_pow(other) {
                        // SAFETY: checked_pow returns None on overflow
                        // so the result cannot be negative.
                        Some(unsafe { $Ty::new_unchecked(result) })
                    } else {
                        None
                    }
                }

                /// Raise non-negative value to an integer power.
                #[doc = concat!(
                    "Return [`", stringify!($Int), "::MIN`] ",
                    "or [`", stringify!($Int), "::MAX`] on overflow."
                )]
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                /// # fn main() { test().unwrap(); }
                /// # fn test() -> Option<()> {
                #[doc = concat!("let three = ", stringify!($Ty), "::new(3)?;")]
                #[doc = concat!("let twenty_seven = ", stringify!($Ty), "::new(27)?;")]
                #[doc = concat!("let max = ", stringify!($Ty), "::new(",
                                stringify!($Int), "::MAX)?;")]
                ///
                /// assert_eq!(twenty_seven, three.saturating_pow(3));
                /// assert_eq!(max, max.saturating_pow(3));
                /// # Some(())
                /// # }
                /// ```
                #[must_use = "this returns the result of the operation, \
                              without modifying the original"]
                #[inline]
                pub const fn saturating_pow(self, other: u32) -> $Ty {
                    // SAFETY: saturating_pow returns u*::MAX on overflow
                    // so the result cannot be negative.
                    unsafe { $Ty::new_unchecked(self.get().saturating_pow(other)) }
                }
            }
        )+
    }
}

non_negative_operations! {
    NonNegativeI8(i8);
    NonNegativeI16(i16);
    NonNegativeI32(i32);
    NonNegativeI64(i64);
    NonNegativeI128(i128);
    NonNegativeIsize(isize);
}

macro_rules! non_negative_min_max {
    ( $( $Ty: ident($Int: ident); )+ ) => {
        $(
            impl $Ty {
                /// The smallest value that can be represented by this non-negative
                /// integer type, 0.
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                #[doc = concat!("assert_eq!(", stringify!($Ty), "::MIN.get(), ","0);")]
                /// ```
                pub const MIN: Self = unsafe { Self::new_unchecked(0) };

                /// The largest value that can be represented by this non-negative
                /// integer type,
                #[doc = concat!("equal to [`", stringify!($Int), "::MAX`].")]
                ///
                /// # Examples
                ///
                /// ```
                #[doc = concat!("# use non_negative::", stringify!($Ty), ";")]
                ///
                #[doc = concat!("assert_eq!(", stringify!($Ty), "::MAX.get(), ", stringify!($Int), "::MAX);")]
                /// ```
                pub const MAX: Self = unsafe { Self::new_unchecked(<$Int>::MAX) };
            }
        )+
    }
}

non_negative_min_max! {
    NonNegativeI8(i8);
    NonNegativeI16(i16);
    NonNegativeI32(i32);
    NonNegativeI64(i64);
    NonNegativeI128(i128);
    NonNegativeIsize(isize);
}

#[cfg(test)]
mod tests {
    use super::*;
}


