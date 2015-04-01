use std::fmt::Result;

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
