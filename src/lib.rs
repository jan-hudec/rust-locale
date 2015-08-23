#![crate_name = "locale"]
#![crate_type = "rlib"]
#![crate_type = "dylib"]

//! Localisation is hard.
//!
//! Getting your program to work well in multiple languages is a world fraught with edge-cases,
//! minor grammatical errors, and most importantly, subtle things that don't map over well that you
//! have absolutely no idea are different in other cultures.
//!
//! Many people are aware of the simpler ones, such as whether to use decimal points or decimal
//! commas, or that the names of the months are different in other languages. But there are also
//! different ways to format dates and times, or variations on what day the week begins. It's
//! perfectly possible to write your program unaware of how these things have to be changed at all,
//! and that's why it's so hard.

extern crate libc;

use std::cmp::max;
use std::default::Default;
use std::fmt::{Display,LowerExp};
use std::io::Result;

/// Describes locale conventions.
///
/// `Locale` is a container for facets that describe how individual locale-dependent operations
/// should be done.
pub struct Locale {
    numeric: Box<Numeric>,
    time: Box<Time>,
}

impl Locale {
    /// Construct specific locale
    ///
    /// How the locale should be constructed is specified by instance of `LocaleFactory`. The
    /// default user locale can be obtained by `default()`.
    pub fn new(factory: &LocaleFactory) -> Locale {
        Locale {
            numeric: if let Some(n) = factory.get_numeric() {
                n
            } else {
                Box::new(Numeric::default())
            },
            time: if let Some(t) = factory.get_time() {
                t
            } else {
                Box::new(Time::default())
            },
        }
    }

    /// Return numeric facet.
    pub fn numeric(&self) -> &Numeric {
        &*self.numeric
    }

    /// Return time facet.
    pub fn time(&self) -> &Time {
        &*self.time
    }

    /// Construct message formatter for this locale.
    pub fn fmt<'a>(&'a self, format: &'a str) -> fmt::MsgFmt<'a> {
        fmt::MsgFmt::new(self, format)
    }
}

impl Default for Locale {
    fn default() -> Self {
        if let Ok(f) = SystemLocaleFactory::new("") {
            Locale::new(&f)
        } else {
            Locale::new(&InvariantLocaleFactory)
        }
    }
}

/// Trait defining how to obtain various components of a locale.
///
/// Use implementation of this trait to construct parts of the `Locale` object.
///
/// There may be various methods for obtaining locale data. The lowest common denominator is
/// standard C library. It is however quite limited and some systems (notably Android) don't
/// actually contain the corresponding data. Many systems also provide additional configurability
/// for the locale setting (Windows, KDE, etc.) that are only accessible via that system's specific
/// interface. So this trait exists to allow combining the methods for obtaining the data.
///
/// The implementations for individual locale categories are returned boxed, because they may need
/// to be polymorphic _and_ in options to allow combining partial implementations. Creating locale
/// data is not a performance critical operation, so dynamic polymrphism is used for sake of
/// simplicity.
///
/// All methods default to simply returning None, again so partial implementations that delegate to
/// another factory are possible. See `CompositeLocaleFactory`.
pub trait LocaleFactory {
    /// Get implementation of the Numeric locale category.
    fn get_numeric(&self) -> Option<Box<Numeric>> { None }

    /// Get implementation of the Time locale category.
    fn get_time(&self) -> Option<Box<Time>> { None }
}

/// Auxiliary class for creating composing partial implementations of locale factories.
// FIXME: Create (doc) test when there actually is another implementation to substitute.
#[derive(Debug, Clone)]
pub struct CompositeLocaleFactory<First: LocaleFactory, Second: LocaleFactory> {
    first: First,
    second: Second,
}

impl<F: LocaleFactory, S: LocaleFactory> CompositeLocaleFactory<F, S> {
    pub fn new(first: F, second: S) -> Self {
        CompositeLocaleFactory::<F, S> {
            first: first, second: second
        }
    }
}

impl<F: LocaleFactory, S: LocaleFactory> LocaleFactory for CompositeLocaleFactory<F, S> {
    // XXX: Make a macro for this
    fn get_numeric(&self) -> Option<Box<Numeric>> {
        if let Some(v) = self.first.get_numeric() {
            Some(v)
        } else {
            self.second.get_numeric()
        }
    }

    fn get_time(&self) -> Option<Box<Time>> {
        if let Some(v) = self.first.get_time() {
            Some(v)
        } else {
            self.second.get_time()
        }
    }
}

/// Factory of invariant locales.
///
/// Invariant locale, called "C" or "POSIX" by standard C library locale functions, is default
/// locale definitions for when no information about desired locale is available or localization is
/// turned off.
#[derive(Debug, Clone, Default)]
pub struct InvariantLocaleFactory;

impl InvariantLocaleFactory {
    /// Constructs invariant locale factory.
    ///
    /// The signature is just so that it matches the other locale factories so the classes can be
    /// substituted depending on target operating system and the code using them does not have to
    /// care.
    #[allow(unused_variables)]
    pub fn new(locale: &str) -> Result<Self> {
        Ok(InvariantLocaleFactory)
    }
}

impl LocaleFactory for InvariantLocaleFactory {
    // NOTE: Yep, it's empty. This just returns nothing and the Locale constructor will take care
    // of the actual defaults.
}

// ---- system specific implementations ----

#[cfg(target_os = "linux")]
pub mod linux;

#[cfg(target_os = "linux")]
pub use linux::LibCLocaleFactory as SystemLocaleFactory;

// FIXME: #[cfg(target_os = "macos")], but for the moment I need to test whether it compiles, don't
// have MacOS box nor cross-compiler and it does not actually contain anything system-specific yet
pub mod macos;

#[cfg(target_os = "macos")]
pub use macos::MacOSLocaleFactory as SystemLocaleFactory;

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub use InvariantLocaleFactory as SystemLocaleFactory;

/// Return LocaleFactory appropriate for default user locale, as far as it can be determined.
///
/// The returned locale factory provides locale facets implemented using standard localization
/// functionality of the underlying operating system and configured for user's default locale.
///
/// **Deprecated:** Use SystemLocaleFactory::default() or better yet simply Locale::default().
pub fn user_locale_factory() -> SystemLocaleFactory {
    // FIXME: Error handling? Constructing locale with "" should never fail as far as I can tell.
    SystemLocaleFactory::new("").unwrap()
}
// ---- formatting ----

pub mod fmt; // The public formatting API and trait implementations
mod fmtutil; // Helper string functions and type-specific formatting

// ---- locale facets ----


// ---- numeric stuff ----

/// Information on how to format numbers.
///
/// **Unstable:** This is likely to be changed to a trait in future. Only use via `fmt::MsgFmt` is
/// stable.
///
/// # Format specifications
///
/// The general form of format specifier is:
///
/// ```ebnf
/// format_spec ::= [[fill]align][sign]["0"][width][.["0"]precision][type]
/// fill        ::= <any character>
/// align       ::= "<" | ">" | "=" | "^"
/// sign        ::= "+" | "-" | " " | "|"
/// width       ::= integer
/// precision   ::= integer
/// type        ::= depends on argument type
/// ```
///
/// The fill and alignment options are:
///
///  - `<`: Align to the logical left.
///  - `>`: Align to the logical right.
///  - `=`: Insert padding between sign and magnitude.
///  - `^`: Centre the field with bias to the logical right.
///
/// The sign options are:
///
///  - `+`: Print `+` for positive and `-` for negative numbers.
///  - `-`: Print nothing for positive and `-` for negative numbers.
///  - space: Print non-breakable space for positive and `-` for negative numbers.
///  - `|`: Do not print sign at all (intended mainly as helper for formatting more complex types).
///
/// If the _width_ starts with `0`, _fill_ is set to `0`.
///
/// _width_ is positive integer defining _minimum_ width of the field. The field will never be
/// truncated.
///
/// The _precision_ specifies number of digits after decimal point for `f` format and number of
/// significant digits for the other floating-point formats. It has no effect for integers.
///
/// If the _precision_ starts with `0`, trailing zeroes _after_ decimal point will be _truncated_.
///
/// ## Integer format types
///
///  - `n`: The default format according to current locale. Can be omitted.
///  - `c`: Use locale digits, but don't insert group separators.
///  - `C`: Not localized. Use latin digits and don't insert group separators.
///
/// ## Floating-point number format types
///
///  - `e`: Engineering exponential format. _precision_ indicates the number of significant digits.
///    Short exponent separator will be used which is `E` in most locales.
///  - `E`: Common exponential format. _precision_ indicates the number of significant digits. Long
///    exponent separator will be used which is usually `×10` and in locales using the latin digits
///    the superscript digits will be used to render the exponent.
///  - `f`: Fixed point representation. _precision_ indicates number of digits after decimal point.
///  - `g`: General representation. _precision_ indicates number of significant digits. Unlike C,
///    the format will _not_ switch to exponential representation for too small or too large
///    numbers.
///  - `h`: General representation with exponential fallback. This will switch to engineering
///    exponential format if insignifiant zeroes would be otherwise needed, that is when the number
///    of digits before decimal point would be larger than number of significant digits or if the
///    first significant digit is lower order than tenths.
///  - `H`: General representation with exponential fallback. Like `h`, but will fall back to
///    common exponential format like `E`.
///  - `m`: Mantissa. Just the mantissa part of the exponential format. For when something needs to
///    be inserted between mantissa and exponent.
///  - `x`: Exponent. Just the exponent part of the exponential format. For when something needs to
///    be inserted between mantissa and exponent.
///  - `X`: Exponent, but in locales with latin digits it will be in superscript.
///
/// ## Examples
// FIXME FIXME FIXME DOCTESTS!
#[derive(Debug, Clone)]
pub struct Numeric {
    /// The punctuation that separates the decimal part of a non-integer number. Usually a decimal
    /// point or a decimal comma.
    pub decimal_sep: String,

    /// The punctuation that separates groups of digits in long numbers.
    pub thousands_sep: String,

    /// Decimal digits in appropriate script.
    pub digits: [char; 10],

    /// Group sizes.
    ///
    /// According to CLDR, there are at most two group sizes, so it is an array to avoid additional
    /// allocation. Primary group is at index 0.
    pub groups: [u8; 2],
}

static LATIN_DIGITS: [char; 10] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
static SUPERSCRIPT_DIGITS: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];

impl Numeric {
    /// Format integral number.
    ///
    /// Ouput should be written to a fomratter. Note, that padding should be used as specified in
    /// `fmt1` or `fmt2`, not as given in `out`.
    ///
    /// # Parameters
    ///  - `n`: The number to format.
    ///  - `fmt1`: First format specification, with higher precedence.
    ///  - `fmt2`: Second format specification, with lower precedence.
    ///  - `out`: Output sink. Don't use the padding defined on it, pad according to `fmt`.
    pub fn format_int_to<I: Display>(&self, n: &I, fmt1: &str, fmt2: &str, out: &mut ::std::fmt::Formatter)
        -> ::std::fmt::Result
    {
        let mut fmt = fmtutil::PythonyPattern::default();
        fmt.fmt = 'n';
        try!(fmt.set(fmt2));
        try!(fmt.set(fmt1));
        fmt.minprec = 0; // do not want precision for integers!
        let digits = match fmt.fmt {
            'n' => &self.digits,
            'c' => { fmt.use_sep = false; &self.digits },
            'C' => { fmt.use_sep = false; &LATIN_DIGITS },
            _ => return Err(::std::fmt::Error),
        };
        let numstr = n.to_string(); // default Display; no options needed for it
        let (neg, not, exp) = fmtutil::split_number_string(&numstr);
        if exp != "" || not.exp != 0 { return Err(::std::fmt::Error); }

        return fmt.format_to(neg, &not, &self, digits, "+", "-", out);
    }

    /// Format floating-point number.
    ///
    /// Ouput should be written to a fomratter. Note, that padding should be used as specified in
    /// `fmt1` or `fmt2`, not as given in `out`.
    ///
    /// # Parameters
    ///  - `n`: The number to format.
    ///  - `fmt1`: First format specification, with higher precedence.
    ///  - `fmt2`: Second format specification, with lower precedence.
    ///  - `out`: Output sink. Don't use the padding defined on it, pad according to `fmt`.
    pub fn format_float_to<I: Display + LowerExp>(&self, n: &I, fmt1: &str, fmt2: &str, out: &mut ::std::fmt::Formatter)
        -> ::std::fmt::Result
    {
        let mut fmt = fmtutil::PythonyPattern::default();
        try!(fmt.set(".06h"));
        try!(fmt.set(fmt2));
        try!(fmt.set(fmt1));
        let mut efmt = fmtutil::PythonyPattern::default();
        efmt.sign = fmtutil::Sign::Always;

        let numstr = match fmt.fmt {
            // number of decimal digits => use Display
            'f' => format!("{:.*}", fmt.maxprec as usize, *n),
            // number of significant digits => use LowerExp
            _ => { fmt.use_sig = true; format!("{:.*e}", fmt.maxprec as usize, *n) },
        };
        let (neg, mut not, exp) = fmtutil::split_number_string(&numstr);

        // Decide whether exponential format will be used and adjust not if yes:
        let use_exp = match fmt.fmt {
            'e'|'E' => true,
            'f'|'g' => false,
            'h'|'H' => not.exp > fmt.maxprec as i32 || not.exp < -1,
            'm' => { not.exp = 0; false } // mutate not as if exponent, but otherwise don't use it
            'x'|'X' => {
                try!(efmt.set(fmt2));
                try!(efmt.set(fmt1));
                efmt.minprec = 0; // exponent does not have fractional part

                let (eneg, enot, eexp) = fmtutil::split_number_string(exp);
                if eexp != "" || enot.exp != 0 { return Err(::std::fmt::Error); }

                if fmt.fmt == 'X' && self.digits[0] == '0' {
                    return efmt.format_to(eneg, &enot, &self, &SUPERSCRIPT_DIGITS, "⁺", "¯", out);
                } else {
                    return efmt.format_to(eneg, &enot, &self, &self.digits, "+", "-", out);
                };
            },
            _ => return Err(::std::fmt::Error),
        };
        if use_exp {
            not.exp = 0; // see Notation.format_to doc
            assert!(!exp.is_empty()); // fmt.fmt is not 'f', so we should have used LowerExp
        };
        let width =
            fmt.sign.width(neg) +
            not.width(1, fmt.min_frac(), fmt.min_sig(), fmt.use_sep, &self);
            if use_exp {
                1 + // FIXME FIXME: long exponent prefix
                exp.len() +
                if exp.starts_with('-') { 0 } else { 1 } // exponent sign
            } else { 0 };
        let padding = max(fmt.minwidth - width, 0);
        // FIXME FIXME: repeating myself from PythonyPattern.format_to; the magic does not work,
        // too
        let fill = if fmt.fill == '0' { self.digits[0] } else { fmt.fill };

        //try!(fmt.format_to(neg, not, &self, &self.digits, "+", "-", out));
        try!(fmt.before_to(padding, fill, out));
        try!(out.write_str(fmt.sign.get(neg, "+", "-")));
        try!(fmt.internal_to(padding, fill, out));
        try!(not.format_to(1, fmt.min_frac(), fmt.min_sig(),
                           fmt.use_sep, &self, &self.digits, out));

        if use_exp {
            try!(out.write_str("e")); // FIXME FIXME: long exponent prefix
            let (eneg, enot, eexp) = fmtutil::split_number_string(exp);
            if eexp != "" || enot.exp != 0 { return Err(::std::fmt::Error); }

            if (fmt.fmt == 'E' || fmt.fmt == 'H') && self.digits[0] == '0' {
                return efmt.format_to(eneg, &enot, &self, &SUPERSCRIPT_DIGITS, "⁺", "¯", out);
            } else {
                return efmt.format_to(eneg, &enot, &self, &self.digits, "+", "-", out);
            };
        };

        return fmt.after_to(padding, fill, out);
    }
    /// Format integral number.
    ///
    /// Ouput should be written to a fomratter. Note, that padding should be used as specified in
    /// `fmt`, not as given in `out`.
    ///
    /// # Parameters
    ///  - `n`: The number to format.
    ///  - `fmt`: Format specification. Implementations _should_ understand at least python-style
    ///     specifications and CLDR patterns.
    ///  - `out`: Output sink. Don't use the padding defined on it, pad according to `fmt`.
    ///
    ///  # Supported format specifications
    ///
    /// **Deprecated:** Obtain from `Locale` or use `SystemLocaleFactory`.
    pub fn load_user_locale() -> Result<Numeric> {
        if let Ok(factory) = SystemLocaleFactory::new("") {
            if let Some(numeric) = factory.get_numeric() {
                return Ok(*numeric);
            }
        }
        Ok(Numeric::english())
    }

    /// **Deprecated:** English is not appropriate default. Use `InvariantLocaleFactory` to get a default instance.
    pub fn english() -> Numeric {
        Numeric::new(".", ",")
    }

    /// **Deprecated:** Use appropriate LocaleFactory to get instance.
    pub fn new(decimal_sep: &str, thousands_sep: &str) -> Numeric {
        Numeric {
            decimal_sep: decimal_sep.to_string(),
            thousands_sep: thousands_sep.to_string(),
            digits: LATIN_DIGITS,
            groups: [3, 3],
        }
    }

    pub fn format_int<I: Display>(&self, input: I) -> String {
        let s = input.to_string();
        let mut buf = String::new();

        for (i, c) in s.chars().enumerate() {
            buf.push(c);
            if (s.len() - i - 1) % 3 == 0 && i != s.len() - 1 {
                buf.push_str(&self.thousands_sep[..]);
            }
        }

        buf
    }

    pub fn format_float<F: Display>(&self, input: F, decimal_places: usize) -> String {
        format!("{:.*}", decimal_places, input).replace(".", &self.decimal_sep)
    }
}

impl Default for Numeric {
    /// Default instance of locale facet corresponds to the *C* locale.
    fn default() -> Self {
        Numeric {
            decimal_sep: ".".to_owned(),
            thousands_sep: "".to_owned(),
            digits: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'],
            groups: [0, 0],
        }
    }
}

// ---- time stuff ---

#[derive(Debug, Clone)]
pub struct Time {
    month_names: Vec<String>,
    long_month_names: Vec<String>,
    day_names: Vec<String>,
    long_day_names: Vec<String>,
}

impl Time {
    pub fn load_user_locale() -> Result<Time> {
        if let Ok(factory) = SystemLocaleFactory::new("") {
            if let Some(time) = factory.get_time() {
                return Ok(*time);
            }
        }
        Ok(Time::english())
    }

    pub fn english() -> Time {
        Time::default()
    }

    pub fn long_month_name(&self, months_from_january: usize) -> String {
        self.long_month_names[months_from_january].clone()
    }

    pub fn short_month_name(&self, months_from_january: usize) -> String {
        self.month_names[months_from_january].clone()
    }

    pub fn long_day_name(&self, days_from_sunday: usize) -> String {
        self.day_names[days_from_sunday].clone()
    }

    pub fn short_day_name(&self, days_from_sunday: usize) -> String {
        self.day_names[days_from_sunday].clone()
    }

}

impl Default for Time {
    fn default() -> Self {
        Time {
            month_names: vec![
                "Jan".to_string(),  "Feb".to_string(),  "Mar".to_string(),
                "Apr".to_string(),  "May".to_string(),  "Jun".to_string(),
                "Jul".to_string(),  "Aug".to_string(),  "Sep".to_string(),
                "Oct".to_string(),  "Nov".to_string(),  "Dec".to_string(),
            ],
            long_month_names: vec![
                "January".to_string(),    "February".to_string(),
                "March".to_string(),      "April".to_string(),
                "May".to_string(),        "June".to_string(),
                "July".to_string(),       "August".to_string(),
                "September".to_string(),  "October".to_string(),
                "November".to_string(),   "December".to_string(),
            ],
            day_names: vec![
                "Sun".to_string(),
                "Mon".to_string(),  "Tue".to_string(),  "Wed".to_string(),
                "Thu".to_string(),  "Fri".to_string(),  "Sat".to_string(),
            ],
            long_day_names: vec![
                "Sunday".to_string(),
                "Monday".to_string(),    "Tuesday".to_string(),  "Wednesday".to_string(),
                "Thursday".to_string(),  "Friday".to_string(),   "Saturday".to_string(),
            ],
        }
    }
}

// ---- tests ----

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn thousands_separator() {
        let numeric_options = Numeric::new("/", "=");
        assert_eq!("1=234=567".to_string(), numeric_options.format_int(1234567))
    }

    #[test]
    fn thousands_separator_2() {
        let numeric_options = Numeric::new("/", "=");
        assert_eq!("123=456".to_string(), numeric_options.format_int(123456))
    }

    #[test]
    fn thousands_separator_3() {
        let numeric_options = Numeric::new("/", "=");
        assert_eq!("12=345=678".to_string(), numeric_options.format_int(12345678))
    }
}
