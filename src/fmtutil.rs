use std::cmp::max;
use std::fmt::{Formatter,Result};
use std::str::FromStr;
use super::Numeric;

/// Generic function for format string processing.
///
/// `format` is the string to proces. `search` is a function that returns index of next substring
/// to substitute and `replace` is a function that returns replacement for substring.
///
/// Based on boost's stralgo finder and formatter.
pub fn search_replace_to<Search, Replace> (format: &str,
                                           search: Search,
                                           replace: Replace,
                                           out: &mut ::std::fmt::Formatter)
    -> Result
    where Search: Fn(&str) -> Option<(usize, usize)>,
        Replace: Fn(&str, &mut ::std::fmt::Formatter) -> Result
{
    let mut haystack = format;
    //fn next_match(haystack: &str) -> Option<(&str, &str, &str)> {
    let next_match = |h| {
        if let Some((begin, end)) = search(h) {
            Some((&h[..begin],
                  &h[begin..end],
                  &h[end..]))
        } else {
            None
        }
    };
    let mut res = Ok(());
    loop {
        if let Some((pre, m, suf)) = next_match(haystack) {
            if let Err(e) = out.write_str(pre) {
                res = Err(e);
            }
            if let Err(e) = replace(m, out) {
                res = Err(e);
            }
            haystack = suf;
        } else {
            if let Err(e) = out.write_str(haystack) {
                res = Err(e);
            }
            break;
        }
    }
    return res;
}

// ---- number formatting ----

fn separator_count(digits: i32, numeric: &Numeric) -> i32 {
    if numeric.groups[0] == 0 || digits <= numeric.groups[0] as i32 {
        return 0;
    }
    if numeric.groups[1] == 0 {
        return 1;
    }
    return 1 + (digits - (numeric.groups[0] as i32) - 1) / (numeric.groups[1] as i32);
}

fn is_time_for_separator(digits_left: i32, numeric: &Numeric) -> bool
{
    if numeric.groups[0] == 0 || digits_left < numeric.groups[0] as i32 {
        return false;
    }
    if digits_left == numeric.groups[0] as i32 {
        return true;
    }
    debug_assert!(digits_left > numeric.groups[0] as i32);
    if numeric.groups[1] == 0 {
        return false;
    }
    return (digits_left - numeric.groups[0] as i32) % numeric.groups[1] as i32 == 0;
}

/// Helper struct for processing mantissa of a stringified number.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Notation<'a> {
    pub int: &'a str,
    pub frac: &'a str,
    pub exp: i32,
}

impl<'a> Notation<'a> {
    /// Returns number of _chars_ the result of `format_to` will have.
    ///
    /// Fortunately numbers don't use anything that would need combining symbols, so number of
    /// characters equals number of glyphs.
    pub fn width(&self, min_int: i32, min_frac: i32, min_sig: i32, use_separators: bool,
                 numeric: &Numeric) -> i32 {
        debug_assert!(min_int >= 0);
        debug_assert!(min_frac >= 0);
        let integral = max(self.int.len() as i32 + self.exp, min_int);
        let fractional = max(self.frac.len() as i32 - self.exp,
                             max(min_sig - self.int.len() as i32 - self.exp,
                                 min_frac));
        // note: since min_int and min_frac are unsigned, integral and fractional are actually
        // nonnegative here.
        return integral + // integral digits will be printed
            if use_separators {
                separator_count(integral, numeric) // and separators if requested
            } else { 0 } +
            if fractional > 0 {
                fractional + 1 // if any fractional, don't forget decimal dot
            } else { 0 };
    }

    /// Applies locale-dependent transformation to number, use specified digits.
    ///
    /// Number will be padded with zeroes from either side as required if the precision is not
    /// sufficient, but this function will _not_ truncate it. That must have already been done when
    /// `Display`ing it to get correct rounding.
    ///
    /// The decimal point will be placed according to the exponent recorded in invocant as
    /// appropriate for number is _plain_ format. For printing in exponential format the exponent
    /// needs to be zeroed out.
    ///
    /// The logic for adding and removing zeroes assumes the exponent is either as read from the
    /// string or zeroed and that any number with non-zero exponent will be normalized in the usual
    /// way to one integral digit. The significant digit logic assumes there are no insignificant
    /// zeroes on the left (satisfied since exponential format is used for rounding to given number
    /// of significant digits)
    ///
    /// Arguments are:
    ///
    ///  - `min_int`: Number will be padded from (logical) left with zeroes to at least this number
    ///    of integral digits.
    ///  - `min_frac`: Number will be padded from (logical) right with zeroes to at least this
    ///    number of fractional digits.
    ///  - `min_sig`: Number will be padded from (logical) right with zeroes to at least this
    ///    number of significant digits.
    ///  - `use_separators`: If true, thousands separators will be places as specified by
    ///    `numeric`.
    ///  - `numeric`: The `Numeric` facet defining thousands and decimal separator and thousands
    ///    separator positions.
    ///  - `digits`: Array of digit characters. In most cases it should be taken from `numeric`,
    ///    but it is given separately so superscript digits (⁰¹²³⁴⁵⁶⁷⁸⁹) can be rendered for
    ///    printing exponents.
    pub fn format_to(&self, min_int: i32, min_frac: i32, min_sig: i32, use_separators: bool,
                     numeric: &Numeric, digits: &[char; 10], out: &mut Formatter) -> Result {
        debug_assert!(min_int >= 0);
        debug_assert!(min_frac >= 0);
        let mut integral = self.int.len() as i32 + self.exp;
        let mut fractional = max(self.frac.len() as i32 - self.exp,
                                 max(min_sig - integral,
                                     min_frac));
        let mut iter = self.int.chars().chain(self.frac.chars());

        let digit = |oc: Option<char>| {
            if let Some(c) = oc {
                digits[c.to_digit(10).expect("non-digit in number") as usize]
            } else {
                digits[0]
            }
        };

        if integral < min_int as i32 {
            for _ in 0..(min_int as i32 - integral) {
                try!(out.write_fmt(format_args!("{}", digits[0])));
            }
        }
        while integral > 0 {
            try!(out.write_fmt(format_args!("{}", digit(iter.next()))));
            integral -= 1;
            if use_separators && is_time_for_separator(integral, numeric) {
                try!(out.write_str(&numeric.thousands_sep));
            }
        }
        if fractional > 0 {
            try!(out.write_str(&numeric.decimal_sep));
            while integral < 0 {
                try!(out.write_fmt(format_args!("{}", digit(iter.next()))));
                integral += 1; fractional -= 1;
            }
            while fractional > 0 {
                try!(out.write_fmt(format_args!("{}", digit(iter.next()))));
                fractional -= 1;
            }
        }
        return Ok(());
    }
}

/// Parse number to sign, mantissa and exponent
///
/// Number must be in the basic integral, floating point or (lower) exponential format, i.e. it
/// must match regular expression `-?[0-9]+(\.[0-9]+)?(e-?[0-9]+)?` and must not contain any
/// unnecessary leading zeroes.
///
/// The number must be already rounded to desired precision, since correct rounding is no longer
/// possible on string representation.
///
/// # Returns
///
/// Tripple of
///  - negative
///  - magnitude as mantissa split to integral and fractional part and value of exponent
///  - exponent string (empty if not present)
///
/// The fractional part has trailing zeroes removed. They will be added back by `Notation.format_to` to
/// fill number of fractional and/or significant digits required.
pub fn split_number_string<'a>(number: &'a str) -> (bool, Notation<'a>, &'a str) {
    let (negative, mag_s) = if number.starts_with('-') {
            (true, &number[1..])
        } else {
            (false, number)
        };
    let (man_s, exp_s, exponent) = if let Some(i) = mag_s.find('e') {
            (&mag_s[..i], &mag_s[i+1..], i32::from_str(&mag_s[i+1..]).unwrap())
        } else {
            (mag_s, "", 0i32)
        };
    let (int_s, frac_s) = if let Some(i) = man_s.find('.') {
            (&man_s[..i], man_s[i+1..].trim_right_matches('0'))
        } else {
            (man_s, "")
        };
    return (negative,
            Notation{
                int: int_s,
                frac: frac_s,
                exp: exponent,
            },
            exp_s);
}

#[cfg(test)]
mod test {
    use super::split_number_string;
    use super::super::Numeric;

    use std::fmt::{Display,Formatter,Result};
    use std::string::ToString;

    // NOTEME: can't be const, because it needs allocation for the strings. And they could almost
    // certainly be just chars; I just don't want to break compatibility just yet.
    fn numeric() -> Numeric {
        Numeric {
            decimal_sep: "/".to_owned(),
            thousands_sep: "=".to_owned(),
            digits: ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'],
            groups: [3, 2],
        }
    }

    struct Disp<F>(F) where F: Fn(&mut Formatter) -> Result;

    impl<F> Display for Disp<F> where F: Fn(&mut Formatter) -> Result {
        fn fmt(&self, out: &mut Formatter) -> Result { self.0(out) }
    }

    #[test]
    fn split_and_format1() {
        let (sign, mag, exp) = split_number_string("2.110e2");
        let n = numeric();
        assert_eq!(false, sign);
        assert_eq!(3, mag.width(1, 0, 0, false, &numeric()));
        assert_eq!("₂₁₁", Disp(|out| mag.format_to(1, 0, 0, false, &n, &n.digits, out)).to_string());
        assert_eq!(5, mag.width(5, 0, 0, false, &numeric()));
        assert_eq!("₀₀₂₁₁", Disp(|out| mag.format_to(5, 0, 0, false, &n, &n.digits, out)).to_string());
        assert_eq!(6, mag.width(0, 0, 5, false, &numeric()));
        assert_eq!("₂₁₁/₀₀", Disp(|out| mag.format_to(0, 0, 5, false, &n, &n.digits, out)).to_string());
        assert_eq!(2, mag.exp);
        assert_eq!("2", exp);
    }

    #[test]
    fn split_and_format2() {
        let (sign, mag, exp) = split_number_string("-112268431.2");
        let n = numeric();
        assert_eq!(true, sign);
        assert_eq!(17, mag.width(1, 4, 0, true, &numeric()));
        assert_eq!("₁₁=₂₂=₆₈=₄₃₁/₂₀₀₀", Disp(|out| mag.format_to(1, 4, 0, true, &n, &n.digits, out)).to_string());
        assert_eq!(14, mag.width(1, 0, 0, true, &numeric()));
        assert_eq!("₁₁=₂₂=₆₈=₄₃₁/₂", Disp(|out| mag.format_to(1, 0, 0, true, &n, &n.digits, out)).to_string());
        assert_eq!(0, mag.exp);
        assert_eq!("", exp);
    }
}
