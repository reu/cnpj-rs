#![no_std]

use arrayvec::{ArrayString, ArrayVec};
use core::char::from_digit;
use core::convert::TryFrom;
use core::fmt;
use core::str::FromStr;

#[cfg(feature = "rand")]
use rand::distributions::{Distribution, Standard, Uniform};
#[cfg(feature = "rand")]
use rand::Rng;

static BLACK_LIST: &'static [[u8; 14]] = &[
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
    [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
    [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
    [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
];

/// Validates the given CNPJ number.
/// ```
/// use cnpj;
///
/// assert!(cnpj::valid("96.769.900/0001-77"));
/// assert!(cnpj::valid("96769900000177"));
/// assert!(!cnpj::valid("96.769.900/0001-78"));
/// ```
pub fn valid<T: AsRef<str>>(cnpj: T) -> bool {
    parse(cnpj).is_ok()
}

/// Parses a CNPJ number.
/// ```
/// use cnpj;
///
/// assert!(cnpj::parse("96.769.900/0001-77").is_ok());
/// assert!(cnpj::parse("96769900000177").is_ok());
/// assert!(cnpj::parse("96.769.900/0001-78").is_err());
/// ```
pub fn parse<T: AsRef<str>>(cnpj: T) -> Result<CNPJ, ParseCNPJError> {
    let cnpj = cnpj.as_ref();

    let digits_count = cnpj.chars().filter(|c| c.is_numeric()).count();

    if digits_count < 7 || digits_count > 14 {
        return Err(ParseCNPJError::InvalidLength);
    }

    let mut digits = cnpj
        .chars()
        .filter_map(|c| c.to_digit(10).map(|d| d as u8))
        .collect::<ArrayVec<u8, 14>>();

    for i in 0..digits.remaining_capacity() {
        digits.insert(i, 0);
    }

    let cnpj = CNPJ {
        digits: digits.into_inner().unwrap(),
    };

    if cnpj.valid() {
        Ok(cnpj)
    } else {
        Err(ParseCNPJError::InvalidChecksum)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum ParseCNPJError {
    InvalidLength,
    InvalidChecksum,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CNPJ {
    digits: [u8; 14],
}

impl CNPJ {
    pub fn digits(&self) -> &[u8; 14] {
        &self.digits
    }

    pub fn formatted(&self) -> ArrayString<18> {
        let d = self
            .digits
            .iter()
            .map(|d| from_digit((*d).into(), 10).unwrap())
            .collect::<ArrayVec<char, 14>>();

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

    pub fn check_digits(&self) -> (&u8, &u8) {
        (&self.digits[12], &self.digits[13])
    }

    fn valid(&self) -> bool {
        if BLACK_LIST.contains(self.digits()) {
            return false;
        }

        let check_digit1 = check_digit(&self.digits[0..12]);
        let check_digit2 = check_digit(&self.digits[0..13]);

        self.check_digits() == (&check_digit1, &check_digit2)
    }
}

fn check_digit(digits: &[u8]) -> u8 {
    let check_sum = digits
        .iter()
        .rev()
        .zip((2..=9).cycle())
        .map(|(i, n)| i * (n as u8))
        .map(|n| n as usize)
        .sum::<usize>();

    match check_sum % 11 {
        n if n < 2 => 0,
        n => 11 - n as u8,
    }
}

impl fmt::Display for CNPJ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for c in self.formatted().chars() {
            write!(f, "{}", c)?;
        }
        Ok(())
    }
}

impl FromStr for CNPJ {
    type Err = ParseCNPJError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse(s)
    }
}

impl TryFrom<&str> for CNPJ {
    type Error = ParseCNPJError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        parse(value)
    }
}

impl TryFrom<[u8; 14]> for CNPJ {
    type Error = ParseCNPJError;

    fn try_from(value: [u8; 14]) -> Result<Self, Self::Error> {
        let cnpj = CNPJ { digits: value };
        if cnpj.valid() {
            Ok(cnpj)
        } else {
            Err(ParseCNPJError::InvalidChecksum)
        }
    }
}

impl fmt::Display for ParseCNPJError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseCNPJError::InvalidChecksum => "invalid CNPJ checksum".fmt(f),
            ParseCNPJError::InvalidLength => "invalid CNPJ lenght".fmt(f),
        }
    }
}

#[cfg(feature = "rand")]
impl Distribution<CNPJ> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> CNPJ {
        let digit = Uniform::from(1..9);
        let mut digits = ArrayVec::<u8, 14>::new();
        for _ in 0..11 {
            digits.push(digit.sample(rng));
        }
        digits.push(check_digit(&digits.as_slice()));
        digits.push(check_digit(&digits.as_slice()));
        CNPJ {
            digits: digits.into_inner().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lol() {
        assert_eq!(check_digit(&[0, 1, 2, 1, 9, 9, 0, 0, 0, 0, 0, 1]), 9);
        assert_eq!(check_digit(&[0, 1, 2, 1, 9, 9, 0, 0, 0, 0, 0, 1, 9]), 7);
    }

    #[test]
    fn it_validates() {
        assert!(valid("96.769.900/0001-77"));
        assert!(!valid("96.769.900/0001-78"));
    }

    #[test]
    fn it_disallow_same_digit_numbers() {
        assert!(!valid("11111111111"));
        assert!(!valid("22222222222"));
        assert!(!valid("33333333333"));
        assert!(!valid("44444444444"));
        assert!(!valid("55555555555"));
        assert!(!valid("66666666666"));
        assert!(!valid("77777777777"));
        assert!(!valid("88888888888"));
        assert!(!valid("99999999999"));
    }

    #[test]
    fn it_parses() {
        let cnpj = parse("96.769.900/0001-77");
        assert!(cnpj.is_ok());
        assert_eq!(cnpj.unwrap().digits(), &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);

        let cnpj = parse("96.769.900/0001-77");
        assert!(cnpj.is_ok());
        assert_eq!(cnpj.unwrap().digits(), &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
    }

    #[test]
    fn it_initializes_with_digits() {
        let cnpj = CNPJ::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);
        assert!(cnpj.is_ok());
        assert_eq!(cnpj.unwrap().digits(), &[9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);

        let cnpj = CNPJ::try_from([9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 8]);
        assert!(cnpj.is_err());
    }

    #[test]
    fn it_pads_numbers_with_less_than_eleven_digits() {
        let cnpj = parse("1.219.900/0001-97").unwrap();
        assert_eq!(cnpj.digits(), &[0, 1, 2, 1, 9, 9, 0, 0, 0, 0, 0, 1, 9, 7]);
    }

    #[test]
    fn it_fails_on_invalid_checksums() {
        let cnpj = parse("96.769.900/0001-78");
        assert!(cnpj.is_err());
        assert_eq!(cnpj.unwrap_err(), ParseCNPJError::InvalidChecksum);
    }

    #[test]
    fn it_formats() {
        let cnpj = parse("96769900000177").unwrap();
        assert_eq!(cnpj.formatted().as_str(), "96.769.900/0001-77");
    }

    #[test]
    #[cfg(feature = "rand")]
    fn it_generates_valid_numbers() {
        use rand;
        let mut rng = rand::thread_rng();
        assert!(valid(rand::thread_rng().gen::<CNPJ>().formatted()));
    }
}
