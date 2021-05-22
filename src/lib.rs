#![no_std]

//! # CNPJ
//!
//! Brazilian CNPJ parsing, validating and formatting library.
//!
//! ```rust
//! # fn main() -> Result<(), cnpj::ParseCnpjError> {
//! use cnpj::Cnpj;
//!
//! // Use the `valid` function if all you need is validating a CNPJ number
//! assert!(cnpj::valid("96769900000177"));
//! assert!(cnpj::valid("96.769.900/0001-77"));
//! assert!(!cnpj::valid("00.000.000/0000-00"));
//!
//! // Parse into a Cnpj struct if you need formatting and other metadata
//! let cnpj: Cnpj = "96769900000177".parse()?;
//! assert_eq!(cnpj.formatted().as_str(), "96.769.900/0001-77");
//! assert_eq!(cnpj.digits(), &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
//!
//! // Note that the Cnpj struct is guaranteed to always be valid
//! assert!("00.000.000/0000-00".parse::<Cnpj>().is_err());
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

use arrayvec::{ArrayString, ArrayVec};
use core::char::from_digit;
use core::convert::TryFrom;
use core::fmt;
use core::str::FromStr;

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
/// let cnpj1 = "96.769.900/0001-77".parse::<Cnpj>()?;
/// let cnpj2 = Cnpj::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7])?;
/// assert_eq!(cnpj1, cnpj2);
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
    /// assert_eq!(cnpj.digits(), &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn digits(&self) -> &[u8; 14] {
        &self.digits
    }

    /// Formats a Cnpj number.
    /// ```rust
    /// # fn main() -> Result<(), cnpj::ParseCnpjError> {
    /// use cnpj::Cnpj;
    ///
    /// let cnpj: Cnpj = "96769900000177".parse()?;
    /// assert_eq!(cnpj.formatted().as_str(), "96.769.900/0001-77");
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note that numbers with less than 14 digits will be padded by zeros.
    /// ```rust
    /// # fn main() -> Result<(), cnpj::ParseCnpjError> {
    /// use cnpj::Cnpj;
    ///
    /// let cnpj: Cnpj = "1.219.900/0001-97".parse()?;
    /// assert_eq!(cnpj.formatted().as_str(), "01.219.900/0001-97");
    /// # Ok(())
    /// # }
    /// ```
    pub fn formatted(&self) -> ArrayString<18> {
        let d = self
            .digits
            .iter()
            .map(|d| from_digit((*d).into(), 10).unwrap())
            .collect::<ArrayVec<char, 18>>();

        let mut fmt = ArrayString::<18>::new();
        fmt.push(d[0]);
        fmt.push(d[1]);
        fmt.push('.');
        fmt.push(d[2]);
        fmt.push(d[3]);
        fmt.push(d[4]);
        fmt.push('.');
        fmt.push(d[5]);
        fmt.push(d[6]);
        fmt.push(d[7]);
        fmt.push('/');
        fmt.push(d[8]);
        fmt.push(d[9]);
        fmt.push(d[10]);
        fmt.push(d[11]);
        fmt.push('-');
        fmt.push(d[12]);
        fmt.push(d[13]);
        fmt
    }
}

fn valid_digits(digits: &[u8; 14]) -> bool {
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

    let mut digits = ArrayVec::<u8, 14>::new();

    for (i, digit) in cnpj
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .enumerate()
    {
        if i == 14 {
            return Err(ParseCnpjError::InvalidLength);
        } else {
            digits.push(digit);
        }
    }

    if digits.len() < 7 {
        return Err(ParseCnpjError::InvalidLength);
    }

    for i in 0..digits.remaining_capacity() {
        digits.insert(i, 0);
    }

    let digits = digits.into_inner().unwrap();

    if valid_digits(&digits) {
        Ok(Cnpj { digits })
    } else {
        Err(ParseCnpjError::InvalidChecksum)
    }
}

impl fmt::Display for Cnpj {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for c in self
            .digits()
            .iter()
            .map(|d| from_digit((*d).into(), 10).unwrap())
        {
            write!(f, "{}", c)?;
        }
        Ok(())
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
        if valid_digits(&value) {
            Ok(Cnpj { digits: value })
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
impl Distribution<Cnpj> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Cnpj {
        let digit = Uniform::from(1..9);
        let mut digits = ArrayVec::<u8, 14>::new();
        for _ in 0..12 {
            digits.push(digit.sample(rng));
        }
        digits.push(check_digit(&digits.as_slice()));
        digits.push(check_digit(&digits.as_slice()));
        Cnpj {
            digits: digits.into_inner().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_validates() {
        assert!(valid("96.769.900/0001-77"));
        assert!(!valid("385.211.390-49"));
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
            &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );

        let cnpj = "96.769.900/0001-77".parse::<Cnpj>();
        assert!(cnpj.is_ok());
        assert_eq!(
            cnpj.unwrap().digits(),
            &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );
    }

    #[test]
    fn it_initializes_with_digits() {
        let cnpj = Cnpj::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
        assert!(cnpj.is_ok());
        assert_eq!(
            cnpj.unwrap().digits(),
            &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]
        );

        let cnpj = Cnpj::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 8]);
        assert!(cnpj.is_err());
    }

    #[test]
    fn it_pads_when_necessary() {
        let cnpj = parse("1.219.900/0001-97").unwrap();
        assert_eq!(cnpj.digits(), &[0, 1, 2, 1, 9, 9, 0, 0, 0, 0, 0, 1, 9, 7]);
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
    fn it_fails_to_parse_numbers_with_more_than_fourteen_digits() {
        let cnpj = "196769900000177".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidLength);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cnpj = "96769900000178".parse::<Cnpj>();
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCnpjError::InvalidChecksum);
    }

    #[test]
    fn it_formats() {
        let cnpj = "96769900000177".parse::<Cnpj>().unwrap();
        assert_eq!(cnpj.formatted().as_str(), "96.769.900/0001-77");
    }

    #[test]
    fn it_display() {
        extern crate std;
        let cnpj = "96.769.900/0001-77".parse::<Cnpj>().unwrap();
        assert_eq!(std::format!("{}", cnpj), "96769900000177");
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        use rand;
        use rand::Rng;
        for _ in 1..10000 {
            let cnpj = rand::thread_rng().gen::<Cnpj>();
            assert!(valid_digits(cnpj.digits()));
        }
    }
}
