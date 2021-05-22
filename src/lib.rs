#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

//! # CNPJ
//!
//! Brazilian CNPJ parsing, validating and formatting library.
//!
//! ```rust
//! # fn main() -> Result<(), cnpj::ParseCnpjError> {
//! use cnpj::Cnpj;
//!
//! // Use the `valid` function if all you need is validating a CNPJ number
//! assert!(cnpj::valid("96.769.900/0001-77"));
//! assert!(cnpj::valid("96769900000177"));
//! assert!(!cnpj::valid("00.000.000/0000-00"));
//!
//! // Parse into a Cnpj struct if you need formatting or other metadata
//! let cnpj: Cnpj = "96769900000177".parse()?;
//! assert_eq!(format!("{}", cnpj), "96.769.900/0001-77");
//! assert_eq!(cnpj.digits(), [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
//!
//! // Note that the Cnpj struct is guaranteed to always be valid
//! assert!("00.000.000/0000-00".parse::<Cnpj>().is_err());
//! assert!(cnpj::valid("96.769.900/0001-77".parse::<Cnpj>()?));
//! # Ok(())
//! # }
//! ```
//!
//! ## no_std support
//!
//! The library can be used on no_std environments by disabling the `std` flag:
//!
//! ```toml
//! [dependencies]
//! cnpj = { version = "0.1", default-features = false }
//! ```
//!
//! ## Random CNPJ generation support
//!
//! The `rand` feature flag enables random CNPJ generation:
//!
//! ```toml
//! [dependencies]
//! cnpj = { version = "0.1", features = ["rand"] }
//! rand = "0.8"
//! ```
//!
//! ```rust
//! # #[cfg(feature = "rand")] {
//! use cnpj::Cnpj;
//! use rand;
//! use rand::Rng;
//!
//! let cnpj: Cnpj = rand::thread_rng().gen();
//! # }
//! ```

use core::convert::TryFrom;
use core::fmt;
use core::str::{from_utf8_unchecked, FromStr};

/// Validates a CNPJ number.
/// ```rust
/// use cnpj;
///
/// assert!(cnpj::valid("96.769.900/0001-77"));
/// assert!(!cnpj::valid("00.000.000/0000-00"));
/// ```
pub fn valid<T: AsRef<str>>(cnpj: T) -> bool {
    parse(cnpj).is_ok()
}

#[derive(Debug, PartialEq, Clone, Hash)]
pub enum ParseCnpjError {
    InvalidLength,
    InvalidChecksum,
}

/// A valid CNPJ number.
///
/// Initialize a `Cnpj` from a `&str` or an array of digits:
/// ```rust
/// # fn main() -> Result<(), cnpj::ParseCnpjError> {
/// # use core::convert::TryFrom;
/// use cnpj::Cnpj;
///
/// let cnpj = "96.769.900/0001-77".parse::<Cnpj>()?;
/// assert_eq!(cnpj.digits(), [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
/// # Ok(())
/// # }
/// ```
///
/// Note that the `Cnpj` struct can only be initialized after a successfully parse,
/// so it is guaranteed to always be valid.
/// ```rust
/// use cnpj::Cnpj;
///
/// let cnpj = "00.000.000/0000-00".parse::<Cnpj>();
/// assert!(cnpj.is_err());
///
/// let cnpj = "96.769.900/0001-77".parse::<Cnpj>().unwrap();
/// assert!(cnpj::valid(cnpj));
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Cnpj {
    digits: [u8; 14],
}

impl Cnpj {
    /// The Cnpj digits.
    /// ```rust
    /// # fn main() -> Result<(), cnpj::ParseCnpjError> {
    /// use cnpj::Cnpj;
    ///
    /// let cnpj: Cnpj = "96.769.900/0001-77".parse()?;
    /// assert_eq!(cnpj.digits(), [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn digits(&self) -> [u8; 14] {
        let mut digits: [u8; 14] = [0; 14];
        for (i, digit) in self.digits.iter().enumerate() {
            digits[i] = digit - 48;
        }
        digits
    }

    /// Returns the (unformatted) CNPJ number.
    /// ```rust
    /// # fn main() -> Result<(), cnpj::ParseCnpjError> {
    /// use cnpj::Cnpj;
    ///
    /// let cnpj: Cnpj = "96.769.900/0001-77".parse()?;
    /// assert_eq!(cnpj.as_str(), "96769900000177");
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note that even being unformatted, the number will be padded by zeros.
    /// ```rust
    /// # fn main() -> Result<(), cnpj::ParseCnpjError> {
    /// use cnpj::Cnpj;
    ///
    /// let cnpj: Cnpj = "1219900000197".parse()?;
    /// assert_eq!(cnpj.as_str(), "01219900000197");
    /// # Ok(())
    /// # }
    /// ```
    pub fn as_str(&self) -> &str {
        // Safety: all the digits are guaranteed to be in ASCII range
        unsafe { from_utf8_unchecked(&self.digits) }
    }

    fn from_valid_digits(digits: [u8; 14]) -> Cnpj {
        let mut ascii_digits: [u8; 14] = [48; 14];
        for (i, digit) in digits.iter().enumerate() {
            ascii_digits[i] = digit + 48;
        }

        Cnpj {
            digits: ascii_digits,
        }
    }
}

fn valid_checksum(digits: &[u8; 14]) -> bool {
    if digits.windows(2).all(|d| d[0] == d[1]) {
        return false;
    }

    [12, 13]
        .iter()
        .all(|d| digits[*d] == check_digit(&digits[0..*d]))
}

fn check_digit(digits: &[u8]) -> u8 {
    let check_sum = digits
        .iter()
        .rev()
        .zip((2..=9).cycle())
        .map(|(i, n)| (i * n) as usize)
        .sum::<usize>();

    match check_sum % 11 {
        n if n < 2 => 0,
        n => 11 - n as u8,
    }
}

fn parse<T: AsRef<str>>(cnpj: T) -> Result<Cnpj, ParseCnpjError> {
    let cnpj = cnpj.as_ref();

    let mut digits: [u8; 14] = [0; 14];

    for (i, digit) in cnpj
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .rev()
        .enumerate()
    {
        if i == 14 {
            return Err(ParseCnpjError::InvalidLength);
        } else {
            digits[13 - i] = digit
        }
    }

    if digits.iter().take_while(|digit| **digit == 0).count() > 10 {
        Err(ParseCnpjError::InvalidLength)
    } else if valid_checksum(&digits) {
        Ok(Cnpj::from_valid_digits(digits))
    } else {
        Err(ParseCnpjError::InvalidChecksum)
    }
}

impl AsRef<str> for Cnpj {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Display for Cnpj {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let digits = self.as_str();
        write!(
            f,
            "{}.{}.{}/{}-{}",
            &digits[0..2],
            &digits[2..5],
            &digits[5..8],
            &digits[8..12],
            &digits[12..14]
        )
    }
}

impl FromStr for Cnpj {
    type Err = ParseCnpjError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse(s)
    }
}

impl TryFrom<&str> for Cnpj {
    type Error = ParseCnpjError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse(value)
    }
}

impl TryFrom<[u8; 14]> for Cnpj {
    type Error = ParseCnpjError;

    fn try_from(value: [u8; 14]) -> Result<Self, Self::Error> {
        if valid_checksum(&value) {
            Ok(Cnpj::from_valid_digits(value))
        } else {
            Err(ParseCnpjError::InvalidChecksum)
        }
    }
}

impl fmt::Display for ParseCnpjError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseCnpjError::InvalidChecksum => "invalid Cnpj checksum".fmt(f),
            ParseCnpjError::InvalidLength => "invalid Cnpj lenght".fmt(f),
        }
    }
}

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
impl std::error::Error for ParseCnpjError {}

#[cfg(feature = "rand")]
use rand::{
    distributions::{Distribution, Standard, Uniform},
    Rng,
};

/// Random CNPJ generation
///
/// ```rust
/// # #[cfg(feature = "rand")] {
/// use cnpj::Cnpj;
/// use rand::Rng;
///
/// let cnpj: Cnpj = rand::thread_rng().gen();
/// # }
/// ```
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
impl Distribution<Cnpj> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Cnpj {
        let digit = Uniform::from(1..9);
        let mut digits: [u8; 14] = [0; 14];
        for d in digits.iter_mut().take(12) {
            *d = digit.sample(rng);
        }
        digits[12] = check_digit(&digits[0..12]);
        digits[13] = check_digit(&digits[0..13]);

        Cnpj::from_valid_digits(digits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_validates() {
        assert!(valid("96.769.900/0001-77"));
        assert!(!valid("96.769.900/0001-78"));
    }

    #[test]
    fn it_disallow_same_digit_numbers() {
        assert!(!valid("11.111.111/1111-11"));
        assert!(!valid("22.222.222/2222-22"));
        assert!(!valid("33.333.333/3333-33"));
        assert!(!valid("44.444.444/4444-44"));
        assert!(!valid("55.555.555/5555-55"));
        assert!(!valid("66.666.666/6666-66"));
        assert!(!valid("77.777.777/7777-77"));
        assert!(!valid("88.888.888/8888-88"));
        assert!(!valid("99.999.999/9999-99"));
    }

    #[test]
    fn it_parses() {
        let cnpj = "96769900000177".parse::<Cnpj>();
        assert!(cnpj.is_ok());
        assert_eq!(
            cnpj.unwrap().digits(),
            [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );

        let cnpj = "96.769.900/0001-77".parse::<Cnpj>();
        assert!(cnpj.is_ok());
        assert_eq!(
            cnpj.unwrap().digits(),
            [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );
    }

    #[test]
    fn it_initializes_with_digits() {
        let cnpj = Cnpj::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
        assert!(cnpj.is_ok());
        assert_eq!(
            cnpj.unwrap().digits(),
            [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );

        let cnpj = Cnpj::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 8]);
        assert!(cnpj.is_err());
    }

    #[test]
    fn it_pads_numbers_with_less_than_eleven_digits() {
        let cnpj = parse("1.219.900/0001-97").unwrap();
        assert_eq!(cnpj.digits(), [0, 1, 2, 1, 9, 9, 0, 0, 0, 0, 0, 1, 9, 7]);
    }

    #[test]
    fn it_fails_to_parse_numbers_that_dont_match_the_min_length() {
        let cnpj = "01".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidLength);

        let cnpj = "0".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidLength);
    }

    #[test]
    fn it_fails_to_parse_numbers_with_more_than_eleven_digits() {
        let cnpj = "196769900000177".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidLength);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cnpj = "38521139038".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidChecksum);
    }

    #[test]
    fn it_display() {
        extern crate std;
        let cnpj = "96769900000177".parse::<Cnpj>().unwrap();
        assert_eq!(std::format!("{}", cnpj), "96.769.900/0001-77");
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        extern crate std;
        use rand;
        use rand::Rng;
        for _ in 1..10000 {
            let cnpj = rand::thread_rng().gen::<Cnpj>();
            assert!(valid(cnpj));
        }
    }
}
