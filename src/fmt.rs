//! Locale-aware formatting.
//!
// FIXME FIXME DOCUMENTME

use super::Locale;
use super::fmtutil;

use std::collections::HashMap;
use std::fmt::{Display,Error,Result};
use std::result::Result::Err;

/// Format an object in a locale-dependent way.
///
/// This trait is similar to `std::fmt::Display` and the other traits in `std::fmt`, except there
/// is just one trait that handles all the formatting parameters itself, because the parameters are
/// inherently different for different types.
///
/// Functions for interpretin formatting parameters for the standard types (numbers, money, dates
/// and times) that can be reused for custom types that contain such types or need similar
/// parameters are available in the `locale::fmt` module.
pub trait Format {
    /// Format the value to output formatter.
    ///
    /// This is the main function used by `locale::fmt::MsgFmt`. It is also the only that must
    /// be implemented when providing implementation for other type.
    ///
    /// # Parameters
    ///
    ///  - `locale`: The locale to format for.
    ///  - `format1`: Format parameters given after `:` in the format string.
    ///  - `format2`: Format parameters given as additional argument.
    ///  - `out`: Output formatter to write the result to.
    ///
    /// `format1` is supposed to take precedence over `format2` if it is not empty.
    fn format_to(&self, locale: &Locale, format1: &str, format2: &str, out: &mut ::std::fmt::Formatter) -> Result;
}

/// Substituting `str` in `locale::fmt::MsgFmt`.
///
/// # Interpreted format parameters
///
/// Currently none.
impl<'a> Format for &'a str {
    fn format_to(&self, _: &Locale, _: &str, _: &str, out: &mut ::std::fmt::Formatter) -> Result {
        // FIXME FIXME padding and stuff
        // TODO One possible format parameter is capitalization - if in some language a word will
        // begin sentence and in other it will not, it should be differently capitalized.
        out.write_str(*self)
    }
}

/// Substituting `String` in `locale::fmt::MsgFmt`.
///
/// See `str` definition.
impl Format for String {
    fn format_to(&self, locale: &Locale, fmt1: &str, fmt2: &str, out: &mut ::std::fmt::Formatter) -> Result {
        (&self[..]).format_to(locale, fmt1, fmt2, out)
    }
}

/// Message formatter.
///
/// # Example
///
/// ```
/// # use locale::Locale;
/// # use std::default::Default;
/// let ape = "orangutan";
/// let food = "bannana";
/// let msg = Locale::default().fmt("The {ape} has a {food}.").arg("ape", &ape).arg("food", &food).to_string();
/// assert_eq!(msg, "The orangutan has a bannana.");
/// ```
pub struct MsgFmt<'a> {
    locale: &'a Locale,
    format: &'a str,
    args: HashMap<&'a str, (&'a Format, &'a str)>,
}

impl<'a> MsgFmt<'a> {
    pub fn new(locale: &'a Locale, format: &'a str) -> Self {
        MsgFmt {
            locale: locale,
            format: format,
            args: HashMap::new(),
        }
    }

    pub fn arg(self, key: &'a str, value: &'a Format) -> MsgFmt<'a> {
        self.argfmt(key, value, "")
    }

    pub fn argfmt(mut self, key: &'a str, value: &'a Format, format: &'a str) -> MsgFmt<'a> {
        let prev = self.args.insert(key, (value, format));
        debug_assert!(prev.is_none(), "Redefinition of format argument '{}'", key);
        return self;
    }

    fn subst_arg(&self, spec: &str, out: &mut ::std::fmt::Formatter) -> Result {
        if spec == "{{" {
            return out.write_str("{");
        }
        if spec == "}}" {
            return out.write_str("}");
        }
        if spec == "}" {
            debug_assert!(false, "Lone }} found in format string");
            return Err(Error);
        }
        debug_assert!(spec.starts_with('{'), "Interal error: pattern does not start with '{{'");
        debug_assert!(spec.ends_with('}'), "Unmatched '{{' in pattern {}", spec);
        let colon = spec.find(':');
        let name = &spec[1 .. colon.unwrap_or(spec.len() - 1)];
        if let Some(argv) = self.args.get(name) {
            let arg : &Format = argv.0;
            let fmt1 : &str = if let Some(i) = colon { &spec[i + 1 .. spec.len() - 1] } else { "" };
            let fmt2 : &str = argv.1;
            return arg.format_to(self.locale, fmt1, fmt2, out);
        } else {
            debug_assert!(false, "Undefined format argument '{}'", name);
            return Err(Error);
        }
    }
}

/// Function to find `{}`-delimited patterns.
fn find_brackets(haystack: &str) -> Option<(usize, usize)>
{
    let mut chi = haystack.char_indices();
    let begin;
    let end = |chi: &mut ::std::str::CharIndices| {
        if let Some((e, _)) = chi.next() { e } else { haystack.len() }
    };

    loop {
        if let Some((i, c)) = chi.next() {
            if c == '{' {
                begin = i;
                break;
            } else if c == '}' {
                begin = i;
                if let Some((j, d)) = chi.next() {
                    if d == '}' {
                        return Some((begin, end(&mut chi)))
                    } else {
                        return Some((begin, j));
                    }
                } else {
                    return Some((begin, haystack.len()));
                }
            }
        } else {
            return None; // No braces found
        }
    }
    // So we have opening brace. Now find the closing one...
    if let Some((_, c)) = chi.next() {
        if c == '{' || c == '}' {
            return Some((begin, end(&mut chi)));
        }
    } else {
        return Some((begin, haystack.len())); // replacer will declare error, searcher can't
    }
    loop {
        if let Some((_, c)) = chi.next() {
            if c == '}' {
                return Some((begin, end(&mut chi)));
            }
        } else {
            return Some((begin, haystack.len())); // replacer will declare error
        }
    }
}

/// The result of message formatting gets output via standard `std::fmt::Formatter`.
impl<'a> Display for MsgFmt<'a> {
    fn fmt(&self, out: &mut ::std::fmt::Formatter) -> Result {
        fmtutil::search_replace_to(
            self.format,
            find_brackets,
            |spec, out| { self.subst_arg(spec, out) },
            out)
    }
}
