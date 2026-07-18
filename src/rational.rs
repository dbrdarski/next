//! Exact rational numbers — the sole Number representation (Compendium B2).
//!
//! Numbers are exact arbitrary-precision rationals; decimal literals denote
//! rationals (`0.5` ≡ 1/2, so `0.1 + 0.2 == 0.3` is **true**). Fixed-precision
//! "decimal" crates are explicitly rejected (Part I step-0). Division is total
//! via Indeterminate values — handled at the `PrimOp` layer, not here.
//!
//! Printing (B2, corrected 1.0.2): a reduced fraction renders as a **decimal**
//! iff its reduced denominator's only prime factors are 2 and 5 (i.e. it divides
//! some power of ten); otherwise it renders as an exact `num/den` fraction.

use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// An exact rational value. Always stored in canonical reduced form with a
/// positive denominator (guaranteed by `num_rational::BigRational`).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Rational(BigRational);

impl Rational {
    /// Construct from a numerator/denominator pair. Reduces to canonical form.
    ///
    /// Panics on a zero denominator: in NEXT `x / 0` is an *Indeterminate value*
    /// produced by the arithmetic layer, never a rational — so a zero
    /// denominator reaching this constructor is a bug, not a language event.
    pub fn new(numer: BigInt, denom: BigInt) -> Self {
        assert!(!denom.is_zero(), "Rational::new called with zero denominator");
        Rational(BigRational::new(numer, denom))
    }

    /// Construct from an integer.
    pub fn from_integer(n: BigInt) -> Self {
        Rational(BigRational::from_integer(n))
    }

    /// Wrap an already-reduced `BigRational` (it reduces on construction anyway).
    pub fn from_ratio(r: BigRational) -> Self {
        Rational(r)
    }

    /// The underlying `BigRational` (already reduced, positive denominator).
    pub fn as_ratio(&self) -> &BigRational {
        &self.0
    }

    /// Parse a decimal literal into an exact rational (B2: literals *denote*
    /// rationals). Accepts an optional sign, integer and/or fractional part
    /// (leading-dot `.5` allowed), and an optional `e`/`E` exponent. Underscore
    /// digit separators are tolerated. This is a value-layer convenience and B2
    /// demonstrator; the lexer (build-order step 2) owns literal diagnostics.
    pub fn from_decimal(s: &str) -> Option<Rational> {
        let s = s.replace('_', "");
        let bytes = s.as_str();
        if bytes.is_empty() {
            return None;
        }

        // Split off an exponent, if any.
        let (mantissa, exp) = match bytes.find(['e', 'E']) {
            Some(i) => {
                let e: i64 = bytes[i + 1..].parse().ok()?;
                (&bytes[..i], e)
            }
            None => (bytes, 0),
        };

        // Sign.
        let (neg, mantissa) = match mantissa.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, mantissa.strip_prefix('+').unwrap_or(mantissa)),
        };

        // Integer / fractional parts.
        let (int_part, frac_part) = match mantissa.find('.') {
            Some(i) => (&mantissa[..i], &mantissa[i + 1..]),
            None => (mantissa, ""),
        };
        if int_part.is_empty() && frac_part.is_empty() {
            return None;
        }
        if !int_part.bytes().all(|b| b.is_ascii_digit())
            || !frac_part.bytes().all(|b| b.is_ascii_digit())
        {
            return None;
        }

        // value = (int_part ++ frac_part) / 10^len(frac_part), then apply exp.
        let digits = format!("{int_part}{frac_part}");
        let numer: BigInt = if digits.is_empty() {
            BigInt::zero()
        } else {
            digits.parse().ok()?
        };
        let mut num = numer;
        let mut den = BigInt::from(10u8).pow(frac_part.len() as u32);
        if exp >= 0 {
            num *= BigInt::from(10u8).pow(exp as u32);
        } else {
            den *= BigInt::from(10u8).pow((-exp) as u32);
        }
        if neg {
            num = -num;
        }
        Some(Rational::new(num, den))
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn is_integer(&self) -> bool {
        self.0.is_integer()
    }
}

/// If `denom` (a positive reduced denominator) divides a power of ten, return
/// `(twos, fives)` — the multiplicities of 2 and 5 in its factorization. Returns
/// `None` when any other prime divides it (⇒ non-terminating decimal). This is
/// the exact B2 predicate.
fn power_of_ten_factors(denom: &BigInt) -> Option<(u32, u32)> {
    let two = BigInt::from(2u8);
    let five = BigInt::from(5u8);
    let mut d = denom.clone();
    let mut twos = 0u32;
    while (&d % &two).is_zero() {
        d /= &two;
        twos += 1;
    }
    let mut fives = 0u32;
    while (&d % &five).is_zero() {
        d /= &five;
        fives += 1;
    }
    if d.is_one() { Some((twos, fives)) } else { None }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let numer = self.0.numer();
        let denom = self.0.denom(); // always positive (BigRational invariant)

        match power_of_ten_factors(denom) {
            // Terminating decimal. Scale numerator so the denominator becomes
            // 10^max(twos,fives); the sign lives on the numerator.
            Some((twos, fives)) => {
                let max = twos.max(fives);
                if max == 0 {
                    // Integer: no fractional digits.
                    return write!(f, "{numer}");
                }
                let scale = BigInt::from(2u8).pow(max - twos) * BigInt::from(5u8).pow(max - fives);
                let scaled = (numer * scale).abs();
                let mut digits = scaled.to_string();
                // Ensure at least max+1 digits so there is a leading integer digit.
                if digits.len() <= max as usize {
                    let pad = max as usize + 1 - digits.len();
                    digits = format!("{}{}", "0".repeat(pad), digits);
                }
                let point = digits.len() - max as usize;
                let (int_str, frac_str) = digits.split_at(point);
                if numer.is_negative() {
                    write!(f, "-{int_str}.{frac_str}")
                } else {
                    write!(f, "{int_str}.{frac_str}")
                }
            }
            // Non-terminating: exact fraction form. Sign rides on the numerator.
            None => write!(f, "{numer}/{denom}"),
        }
    }
}

// Exact arithmetic. Division here is ordinary rational division and is *not*
// total — a zero divisor panics. The language's total division (`x/0` ⇒
// Indeterminate) is a `PrimOp` rule (semantics §3), layered above this type.
impl Add for Rational {
    type Output = Rational;
    fn add(self, rhs: Rational) -> Rational {
        Rational(self.0 + rhs.0)
    }
}
impl Sub for Rational {
    type Output = Rational;
    fn sub(self, rhs: Rational) -> Rational {
        Rational(self.0 - rhs.0)
    }
}
impl Mul for Rational {
    type Output = Rational;
    fn mul(self, rhs: Rational) -> Rational {
        Rational(self.0 * rhs.0)
    }
}
impl Div for Rational {
    type Output = Rational;
    fn div(self, rhs: Rational) -> Rational {
        assert!(!rhs.is_zero(), "Rational::div by zero — total division is a PrimOp rule");
        Rational(self.0 / rhs.0)
    }
}
impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational(-self.0)
    }
}

impl From<i64> for Rational {
    fn from(n: i64) -> Rational {
        Rational::from_integer(BigInt::from(n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64, d: i64) -> Rational {
        Rational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn exactness_flagship() {
        // The seed: 0.1 + 0.2 == 0.3 is true (B2 / conformance seeds).
        let a = Rational::from_decimal("0.1").unwrap();
        let b = Rational::from_decimal("0.2").unwrap();
        let c = Rational::from_decimal("0.3").unwrap();
        assert_eq!(a + b, c);
    }

    #[test]
    fn b2_printing_terminating() {
        assert_eq!(r(1, 2).to_string(), "0.5");
        assert_eq!(r(3, 20).to_string(), "0.15");
        assert_eq!(r(1, 4).to_string(), "0.25");
        assert_eq!(r(2, 5).to_string(), "0.4");
        assert_eq!(r(1, 40).to_string(), "0.025");
        assert_eq!(r(5, 2).to_string(), "2.5");
    }

    #[test]
    fn b2_printing_non_terminating() {
        assert_eq!(r(1, 3).to_string(), "1/3");
        assert_eq!(r(2, 7).to_string(), "2/7");
    }

    #[test]
    fn b2_printing_integers() {
        assert_eq!(Rational::from(3).to_string(), "3");
        assert_eq!(Rational::from(0).to_string(), "0");
        assert_eq!(r(10, 5).to_string(), "2"); // reduces to integer
    }

    #[test]
    fn b2_printing_negatives() {
        assert_eq!(r(-1, 2).to_string(), "-0.5");
        assert_eq!(r(-1, 3).to_string(), "-1/3");
        assert_eq!(r(1, -2).to_string(), "-0.5"); // sign normalizes to numerator
    }

    #[test]
    fn decimal_round_trips() {
        // 0.5 → 1/2 → "0.5"
        assert_eq!(Rational::from_decimal("0.5").unwrap().to_string(), "0.5");
        assert_eq!(Rational::from_decimal("0.15").unwrap().to_string(), "0.15");
        // trailing zeros in the literal do not survive canonicalization
        assert_eq!(Rational::from_decimal("0.30").unwrap(), r(3, 10));
        // leading-dot and exponent forms
        assert_eq!(Rational::from_decimal(".5").unwrap(), r(1, 2));
        assert_eq!(Rational::from_decimal("1e2").unwrap(), Rational::from(100));
        assert_eq!(Rational::from_decimal("15e-2").unwrap(), r(3, 20));
    }
}
