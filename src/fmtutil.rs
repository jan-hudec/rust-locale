use std::cmp::max;
use std::default::Default;
use std::fmt::{Error,Formatter,Result};
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

fn parse_char(s: &str) -> (Option<char>, &str) {
    let mut chi = s.char_indices();
    if let Some((_, c)) = chi.next() {
        if let Some((i, _)) = chi.next() {
            return (Some(c), &s[i..]);
        } else {
            return (Some(c), &s[s.len()..]);
        }
    } else {
        return (None, s);
    }
}

fn parse_flag(flag: char, s: &str) -> (bool, &str) {
    if s.starts_with(flag) {
        (true, parse_char(s).1)
    } else {
        (false, s)
    }
}

fn parse_any<Pred: Fn(char) -> bool>(pred: Pred, s: &str) -> (Option<char>, &str) {
    match parse_char(s) {
        (Some(c), r) if pred(c) => { return (Some(c), r) },
        _ => { return (None, s) },
    }
}

fn parse_any_of<'a>(flags: &[char], s: &'a str) -> (Option<char>, &'a str) {
    parse_any(|c| { flags.contains(&c) }, s)
}

fn parse_all<Pred: Fn(char) -> bool>(pred: Pred, s: &str) -> (&str, &str) {
    let mut chi = s.char_indices();
    loop {
        if let Some((i, c)) = chi.next() {
            if !pred(c) {
                return (&s[..i], &s[i..]);
            }
        } else {
            return (s, &s[s.len()..]);
        }
    }
}

fn parse_all_of<'a>(chars: &[char], s: &'a str) -> (&'a str, &'a str) {
    parse_all(|c| { chars.contains(&c) }, s)
}

fn parse_all_not_of<'a>(chars: &[char], s: &'a str) -> (&'a str, &'a str) {
    parse_all(|c| { !chars.contains(&c) }, s)
}

fn parse_unsigned<T: FromStr>(s: &str) -> (Option<T>, &str) {
    let mut chi = s.char_indices();
    let end;
    loop {
        match chi.next() {
            Some((_, c)) if c.is_digit(10) => { },
            Some((i, _)) => { end = i; break; },
            None => { end = s.len(); break; },
        }
    }
    if end == 0 {
        return (None, &s);
    }
    if let Ok(res) = T::from_str(&s[..end]) {
        return (Some(res), &s[end..]);
    } else {
        return (None, &s);
    }
}

fn parse_int<T: FromStr>(mut s: &str) -> (Option<T>, &str) {
    let mut chi = s.char_indices();
    let end;
    match chi.next() {
        Some((_, '+')) => { s = &s[1..]; chi = s.char_indices(); },
        Some((_, '-')) => { },
        Some((_, c)) if c.is_digit(10) => { },
        _ => { return (None, &s) },
    }
    loop {
        match chi.next() {
            Some((_, c)) if c.is_digit(10) => { },
            Some((i, _)) => { end = i; break; },
            None => { end = s.len(); break; },
        }
    }
    assert!(end != 0);
    if let Ok(res) = T::from_str(&s[..end]) {
        return (Some(res), &s[end..]);
    } else {
        return (None, &s);
    }
}

trait Shiftable<'a> {
    fn shift<Res, Parse>(&mut self, parse: Parse) -> Res
        where Parse: Fn(&'a str) -> (Res, &'a str);

    fn shift_char(&mut self) -> Option<char> {
        self.shift(parse_char)
    }
}

impl<'a> Shiftable<'a> for &'a str {
    fn shift<'b, Res, Parse>(&'b mut self, parse: Parse) -> Res
        where Parse: Fn(&'a str) -> (Res, &'a str)
    {
        let (val, rest) = parse(*self);
        *self = rest;
        return val;
    }
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Alignment { Left, Right, Internal, Centre, }

fn parse_alignment(s: &str) -> ((Option<char>, Option<Alignment>), &str) {
    fn alignment(f: Option<char>, s: &str) -> ((Option<char>, Option<Alignment>), &str) {
        match parse_char(s) {
            (Some('<'), t) => ((f, Some(Alignment::Left)), t),
            (Some('>'), t) => ((f, Some(Alignment::Right)), t),
            (Some('='), t) => ((f, Some(Alignment::Internal)), t),
            (Some('^'), t) => ((f, Some(Alignment::Centre)), t),
            _ => { ((None, None), s) },
        }
    }

    if let (Some(f), t) = parse_char(s) {
        match alignment(Some(f), t) {
            ((_, Some(a)), u) => ((Some(f), Some(a)), u),
            ((_, None), _) => alignment(None, s),
        }
    } else {
        ((None, None), s)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Sign { Always, Negative, Pad, Never, }

fn parse_sign(s: &str) -> (Option<Sign>, &str) {
    match parse_char(s) {
        (Some('+'), t) => (Some(Sign::Always), t),
        (Some('-'), t) => (Some(Sign::Negative), t),
        (Some(' '), t) => (Some(Sign::Pad), t),
        (Some('|'), t) => (Some(Sign::Never), t),
        _ => (None, s),
    }
}

fn parse_precision(s: &str) -> (Option<(i32, i32)>, &str) {
    if let (Some('.'), t) = parse_char(s) {
        let zero = parse_flag('0', t).0;
        if let (Some(prec), u) = parse_unsigned(t) {
            if zero {
                return (Some((0, prec)), u);
            } else {
                return (Some((prec, prec)), u);
            }
        }
    }
    return (None, s);
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PythonyPattern {
    pub fill: char,
    pub alignment: Alignment,
    pub sign: Sign,
    pub minwidth: i32,
    pub minprec: i32,
    pub maxprec: i32,
    pub fmt: char,
}

impl PythonyPattern {
    // NOTE: Parts not specified in the format are not modified. This allows combining the formats.
    // NOTE: The value may be modified even if error is returned. It is not expected to be used
    // then anyway.
    pub fn set(&mut self, mut fmt: &str) -> Result {
        if let (of, Some(a)) = fmt.shift(parse_alignment) {
            if let Some(f) = of { self.fill = f; }
            self.alignment = a;
        }
        if let Some(s) = fmt.shift(parse_sign) {
            self.sign = s;
        }
        if fmt.shift(|s| parse_flag('0', s)) {
            self.fill = '0';
            self.alignment = Alignment::Internal;
        }
        if let Some(w) = fmt.shift(parse_unsigned) {
            self.minwidth = w;
        }
        if let Some((minp, maxp)) = fmt.shift(parse_precision) {
            self.minprec = minp;
            self.maxprec = maxp;
        }
        if let Some(f) = fmt.shift(parse_char) {
            self.fmt = f;
        }
        if fmt.is_empty() {
            Ok(())
        } else {
            Err(Error)
        }
    }
}

impl Default for PythonyPattern {
    // NOTE: The default pattern won't work anywhere, because it has invalid format char!
    fn default() -> Self {
        PythonyPattern {
            fill: ' ',
            alignment: Alignment::Left,
            sign: Sign::Negative,
            minwidth: 0,
            minprec: 0,
            maxprec: 255,
            fmt: '\0',
        }
    }
}

#[cfg(test)]
mod test {
    use super::Shiftable;
    use super::{parse_char,parse_flag,parse_any,parse_all_of,parse_any_of,parse_all_not_of};
    use super::{parse_unsigned,parse_int};
    use super::split_number_string;
    use super::{Alignment,Sign,parse_alignment,parse_sign,parse_precision,PythonyPattern};
    use super::super::Numeric;

    use std::default::Default;

    // --- shift ---

    #[test]
    fn shifts() {
        let mut s = "whatever";
        assert_eq!(Some('w'), s.shift(parse_char));
        assert_eq!(Some('h'), s.shift_char());
        assert_eq!(false, s.shift(|s| { parse_flag('x', s) }));
        assert_eq!(true, s.shift(|s| { parse_flag('a', s) }));
        assert_eq!("", s.shift(|s| { parse_all_of(&['x', 'y', 'z'], s) }));
        assert_eq!(Some('t'), s.shift(|s| { parse_any_of(&['t', 'u', 'v'], s) }));
        assert_eq!(None, s.shift(|s| { parse_any_of(&[], s) }));
        assert_eq!("eve", s.shift(|s| { parse_all_of(&['e', 'l', 'v', 'w'], s) }));
        assert_eq!("r", s);
        assert_eq!(("r", ""), parse_all_not_of(&['a', 'b', 'c'], s));
        assert_eq!(Some('r'), s.shift(|s| { parse_any(|_| { true }, s) }));
        assert_eq!(None, s.shift(|s| { parse_any(|_| { true }, s) }));
        assert_eq!(None, s.shift(|s| { parse_any(|_| { true }, s) }));
    }

    #[test]
    fn shift_num() {
        let mut s = "+2+3-5,211-6";
        assert_eq!(None, s.shift(parse_unsigned::<u32>));
        assert_eq!(Some(2), s.shift(parse_int));
        assert_eq!(Some(3), s.shift(parse_int));
        assert_eq!(None, s.shift(parse_unsigned::<usize>));
        assert_eq!(Some(-5), s.shift(parse_int));
        assert_eq!(None, s.shift(parse_int::<isize>));
        assert_eq!(Some(','), s.shift_char());
        assert_eq!(Some(211), s.shift(parse_int));
        assert_eq!(Some('-'), s.shift_char());
        assert_eq!(Some(6), s.shift(parse_int));
        assert_eq!("", s);
        assert_eq!(None, s.shift(parse_int::<isize>));
        assert_eq!(None, s.shift(parse_unsigned::<usize>));
    }

    // --- number formatting ---

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

    #[test]
    fn pythony_pattern() {
        assert_eq!(((None, None), ""), parse_alignment(""));
        assert_eq!(((None, None), "xy"), parse_alignment("xy"));
        assert_eq!(((None, Some(Alignment::Left)), "xy"), parse_alignment("<xy"));
        assert_eq!(((None, Some(Alignment::Right)), "xy"), parse_alignment(">xy"));
        assert_eq!(((None, Some(Alignment::Internal)), "xy"), parse_alignment("=xy"));
        assert_eq!(((None, Some(Alignment::Centre)), "xy"), parse_alignment("^xy"));
        assert_eq!(((Some('x'), Some(Alignment::Left)), "xy"), parse_alignment("x<xy"));
        assert_eq!(((Some('x'), Some(Alignment::Right)), "xy"), parse_alignment("x>xy"));
        assert_eq!(((Some('x'), Some(Alignment::Internal)), "xy"), parse_alignment("x=xy"));
        assert_eq!(((Some('x'), Some(Alignment::Centre)), "xy"), parse_alignment("x^xy"));
        assert_eq!(((Some('<'), Some(Alignment::Left)), "xy"), parse_alignment("<<xy"));
        assert_eq!(((Some('>'), Some(Alignment::Right)), "xy"), parse_alignment(">>xy"));
        assert_eq!(((Some('='), Some(Alignment::Internal)), "xy"), parse_alignment("==xy"));
        assert_eq!(((Some('^'), Some(Alignment::Centre)), "xy"), parse_alignment("^^xy"));

        assert_eq!((None, "02"), parse_sign("02"));
        assert_eq!((Some(Sign::Always), "02"), parse_sign("+02"));
        assert_eq!((Some(Sign::Negative), "02"), parse_sign("-02"));
        assert_eq!((Some(Sign::Pad), "02"), parse_sign(" 02"));
        assert_eq!((Some(Sign::Never), "02"), parse_sign("|02"));

        assert_eq!((None, "02"), parse_precision("02"));
        assert_eq!((None, "..02"), parse_precision("..02"));
        assert_eq!((None, ".x"), parse_precision(".x"));
        assert_eq!((Some((0, 2)), ""), parse_precision(".02"));
        assert_eq!((Some((2, 2)), ""), parse_precision(".2"));
        assert_eq!((Some((42, 42)), "+xy"), parse_precision(".42+xy"));

        let mut p = PythonyPattern::default();
        assert!(p.set("+2i").is_ok());
        assert_eq!(PythonyPattern{
            fill: ' ', alignment: Alignment::Left, sign: Sign::Always,
            minwidth: 2, minprec: 0, maxprec: 255, fmt: 'i'}, p);
        assert!(p.set("->5j").is_ok());
        assert_eq!(PythonyPattern{
            fill: '-', alignment: Alignment::Right, sign: Sign::Always,
            minwidth: 5, minprec: 0, maxprec: 255, fmt: 'j'}, p);
        assert!(p.set("0.02").is_ok());
        assert_eq!(PythonyPattern{
            fill: '0', alignment: Alignment::Internal, sign: Sign::Always,
            minwidth: 5, minprec: 0, maxprec: 2, fmt: 'j'}, p);
        assert!(p.set("xx").is_err());
        assert_eq!(PythonyPattern{
            fill: '0', alignment: Alignment::Internal, sign: Sign::Always,
            minwidth: 5, minprec: 0, maxprec: 2, fmt: 'x'}, p);
    }
}
