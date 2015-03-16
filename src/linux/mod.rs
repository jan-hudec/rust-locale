//! Locale implementation using GNU libc

use ::std::sync::Arc;
use ::std::borrow::Cow;
use ::std::io::{Error,Result};
use super::{LocaleFactory,Numeric,Time};

pub mod ffi;

/// Wrapper for libc's locale_t.
pub struct CLocale {
    c_locale: ffi::locale_t,
}

impl CLocale {
    /// Constructs new complete locale.
    ///
    /// Constructs `CLocale` with all categories from locale `locale`. See
    /// [`newlocale`](http://man7.org/linux/man-pages/man3/newlocale.3.html).
    pub fn new(locale: &str) -> Result<Self> {
        let cloc = try!(::std::ffi::CString::new(locale));
        let res = unsafe { ffi::newlocale(ffi::LC_ALL_MASK, cloc.as_ptr(), ::std::ptr::null_mut()) };
        if res.is_null() {
            Err(Error::last_os_error())
        } else {
            Ok(CLocale { c_locale: res, })
        }
    }

    /// Constructs new complete locale.
    ///
    /// Constructs `CLocale` with specified categories from locale `locale` and the rest
    /// from `from`. `from` is destroyed in the process. See
    /// [`newlocale`(3)](http://man7.org/linux/man-pages/man3/newlocale.3.html).
    pub fn new_from(mask: ::libc::c_int, locale: &str, mut from: Self) -> Result<CLocale> {
        let cloc = try!(::std::ffi::CString::new(locale));
        let res = unsafe { ffi::newlocale(mask, cloc.as_ptr(), from.c_locale) };
        // XXX: Is there better way to skip Drop then zeroing+check? And the associated need to
        // have the field mut though it's otherwise not needed and not desired?
        from.c_locale = ::std::ptr::null_mut();
        if res.is_null() {
            Err(Error::last_os_error())
        } else {
            Ok(CLocale { c_locale: res, })
        }
    }

    /// Returns locale data item.
    ///
    /// Returns given locale data item. Remember, that the result is encoded in the locale
    /// encoding, which may not be utf-8. To find what the locale charset is, query `langinfo` for
    /// `ffi::CODESET`. See
    /// [`nl_langinfo`(3)](http://man7.org/linux/man-pages/man3/nl_langinfo.3.html)
    pub fn langinfo<'a>(&'a self, item: ::libc::c_uint) -> &'a ::std::ffi::CStr {
        unsafe {
            let res = ffi::nl_langinfo_l(item, self.c_locale);
            ::std::ffi::CStr::from_ptr(res)
        }
    }
}

impl Drop for CLocale {
    fn drop(&mut self) {
        if !self.c_locale.is_null() {
            unsafe { ffi::freelocale(self.c_locale) };
        }
    }
}

impl Clone for CLocale {
    fn clone(&self) -> Self {
        CLocale {
            c_locale: unsafe { ffi::duplocale(self.c_locale) },
        }
    }
}

pub struct IConv {
    iconv: ffi::iconv_t,
}

/// Wrapper for iconv.
///
/// See [`iconv`(3)](http://man7.org/linux/man-pages/man3/iconv.3.html).
/// 
/// On Linux this is part of standard C library and should always be able to convert any charset
/// that the locale component presents, so we can conveniently use it for translating that to the
/// Rust's internal utf-8 encoding there.
impl IConv {
    /// Construct iconv converter.
    ///
    /// See [`iconv_open`(3)](http://man7.org/linux/man-pages/man3/iconv_open.3.html).
    pub fn new(to: &str, from: &str) -> Result<Self> {
        let cto = try!(::std::ffi::CString::new(to));
        let cfrom = try!(::std::ffi::CString::new(from));
        let res = unsafe { ffi::iconv_open(cto.as_ptr(), cfrom.as_ptr()) };
        if res.is_null() {
            Err(Error::last_os_error())
        } else {
            Ok(IConv { iconv: res, })
        }
    }

    /// Convert data with iconv
    ///
    /// See [`iconv`(3)](http://man7.org/linux/man-pages/man3/iconv.3.html). The parameters are
    ///
    ///  1. `src`: The input buffer.
    ///  2. `dst`: The output buffer.
    ///
    /// Return values are:
    ///
    ///  1. Result of `iconv`. If -1, the reason can be read from `errno` (unfortunately
    ///     `::std::io::Error::last_os_error()` does not seem to be able to distinguish them at the
    ///     moment).
    ///  2. Number of bytes processed from `src`.
    ///  3. Number of bytes written to `dst`.
    ///
    /// The C interface returns the remaining buffers instead, but that is actually hard to work
    /// with in Rust.
    pub fn convert(&self, src: &[u8], dst: &mut [u8]) -> (isize, usize, usize) {
        let mut inptr: *const ::libc::c_char = src.as_ptr() as *const ::libc::c_char;
        let mut insize: ::libc::size_t = src.len() as ::libc::size_t;
        let mut outptr: *mut ::libc::c_char = dst.as_ptr() as *mut ::libc::c_char;
        let mut outsize: ::libc::size_t = dst.len() as ::libc::size_t;
        // XXX: Do we need error handling? We don't expect errors and can't do much about them here.
        let res = unsafe {
            ffi::iconv(self.iconv,
                &mut inptr, &mut insize,
                &mut outptr, &mut outsize)
        };
        (res as isize, src.len() - (insize as usize), dst.len() - (outsize as usize))
    }
}

impl Drop for IConv {
    fn drop(&mut self) {
        if !self.iconv.is_null() {
            unsafe { ffi::iconv_close(self.iconv); }
        }
    }
}

#[derive(Clone)]
pub struct LibCLocaleFactory {
    locale: Arc<CLocale>,
    iconv: Option<Arc<IConv>>,
}

impl LibCLocaleFactory {
    // TODO TODO: Try to construct locale with CTYPE overriden to C.UTF-8 and check whether the
    // returned values now appear in UTF-8. Than we wouldn't need the conversion.
    // TODO TODO: Could also try overriding all components to their corresponding UTF-8 variants,
    // though that's quite a bit more work.
    pub fn new(locale: &str) -> Result<Self> {
        let loc = Arc::new(try!(CLocale::new(locale)));
        let ccodeset = loc.langinfo(ffi::CODESET);
        let mut iconv = None;
        if let Ok(codeset) = ::std::str::from_utf8(ccodeset.to_bytes()) {
            if codeset != "UTF-8" {
                if let Ok(i) = IConv::new("UTF-8", codeset) {
                    iconv = Some(Arc::new(i));
                }
            }
        }
        return Ok(LibCLocaleFactory{
            locale: loc.clone(), // It says it's borrowed, but this is the last statement...
            iconv: iconv,
        });
    }

    pub fn langinfo<'a>(&'a self, item: ::libc::c_uint) -> Cow<'a, str> {
        let cres: &'a ::std::ffi::CStr = self.locale.langinfo(item);
        if let &Some(ref iconv) = &self.iconv {
            let mut buf = Vec::new();
            buf.resize(4 * cres.to_bytes().len(), 0u8);
            let conv = iconv.convert(cres.to_bytes(), &mut buf);
            buf.resize(conv.2, 0u8);
            if let Ok(s) = String::from_utf8(buf) {
                return Cow::Owned(s);
            }
        }
        return String::from_utf8_lossy(cres.to_bytes());
    }
}

impl LocaleFactory for LibCLocaleFactory {
    fn get_numeric(&mut self) -> Option<Box<Numeric>> {
        return Some(
            Box::new(
                Numeric::new(
                    &self.langinfo(ffi::RADIXCHAR),
                    &self.langinfo(ffi::THOUSEP))));
    }

    fn get_time(&mut self) -> Option<Box<Time>> {
        return Some(
            Box::new(
                Time {
                    month_names: vec![
                        self.langinfo(ffi::ABMON_1).into_owned(),
                        self.langinfo(ffi::ABMON_2).into_owned(),
                        self.langinfo(ffi::ABMON_3).into_owned(),
                        self.langinfo(ffi::ABMON_4).into_owned(),
                        self.langinfo(ffi::ABMON_5).into_owned(),
                        self.langinfo(ffi::ABMON_6).into_owned(),
                        self.langinfo(ffi::ABMON_7).into_owned(),
                        self.langinfo(ffi::ABMON_8).into_owned(),
                        self.langinfo(ffi::ABMON_9).into_owned(),
                        self.langinfo(ffi::ABMON_10).into_owned(),
                        self.langinfo(ffi::ABMON_11).into_owned(),
                        self.langinfo(ffi::ABMON_12).into_owned(),
                    ],
                    long_month_names: vec![
                        self.langinfo(ffi::MON_1).into_owned(),
                        self.langinfo(ffi::MON_2).into_owned(),
                        self.langinfo(ffi::MON_3).into_owned(),
                        self.langinfo(ffi::MON_4).into_owned(),
                        self.langinfo(ffi::MON_5).into_owned(),
                        self.langinfo(ffi::MON_6).into_owned(),
                        self.langinfo(ffi::MON_7).into_owned(),
                        self.langinfo(ffi::MON_8).into_owned(),
                        self.langinfo(ffi::MON_9).into_owned(),
                        self.langinfo(ffi::MON_10).into_owned(),
                        self.langinfo(ffi::MON_11).into_owned(),
                        self.langinfo(ffi::MON_12).into_owned(),
                    ],
                    day_names: vec![
                        self.langinfo(ffi::ABDAY_1).into_owned(),
                        self.langinfo(ffi::ABDAY_2).into_owned(),
                        self.langinfo(ffi::ABDAY_3).into_owned(),
                        self.langinfo(ffi::ABDAY_4).into_owned(),
                        self.langinfo(ffi::ABDAY_5).into_owned(),
                        self.langinfo(ffi::ABDAY_6).into_owned(),
                        self.langinfo(ffi::ABDAY_7).into_owned(),
                    ],
                    long_day_names: vec![
                        self.langinfo(ffi::DAY_1).into_owned(),
                        self.langinfo(ffi::DAY_2).into_owned(),
                        self.langinfo(ffi::DAY_3).into_owned(),
                        self.langinfo(ffi::DAY_4).into_owned(),
                        self.langinfo(ffi::DAY_5).into_owned(),
                        self.langinfo(ffi::DAY_6).into_owned(),
                        self.langinfo(ffi::DAY_7).into_owned(),
                    ],
                }));
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // ---- tests for CLocale ----

    fn langinfo(loc: &CLocale, item: ::libc::c_uint) -> &str {
        let res = loc.langinfo(item);
        ::std::str::from_utf8(res.to_bytes()).unwrap()
    }

    #[test]
    fn c_locale() {
        let l = CLocale::new("C.UTF-8").unwrap();
        assert_eq!("UTF-8", langinfo(&l, ffi::CODESET));
    }

    #[test]
    fn en_locale() {
        if let Ok(l) = CLocale::new("en_GB") {
            // only test if the host has cs_CZ (non-unicode) locale (travis boxen don't)
            assert_eq!("ISO-8859-1", langinfo(&l, ffi::CODESET));
        }
    }

    #[test]
    fn bad_locale() {
        let l = CLocale::new("wrong");
        assert!(l.is_err());
    }

    #[test]
    fn mixed_locale() {
        if let Ok(l) = CLocale::new("cs_CZ") {
            // only test if the host has these locales (travis boxen don't)
            assert_eq!(",", langinfo(&l, ffi::RADIXCHAR));
            assert_eq!("Po", langinfo(&l, ffi::ABDAY_2));
            if let Ok(m) = CLocale::new_from(ffi::LC_NUMERIC_MASK, "en_GB", l) {
                assert_eq!(".", langinfo(&m, ffi::RADIXCHAR));
                assert_eq!("Po", langinfo(&m, ffi::ABDAY_2));
                if let Ok(n) = CLocale::new_from(ffi::LC_TIME_MASK, "de_DE", m.clone()) {
                    assert_eq!(".", langinfo(&n, ffi::RADIXCHAR));
                    assert_eq!("Mi", langinfo(&n, ffi::ABDAY_4));
                    assert_eq!(".", langinfo(&m, ffi::RADIXCHAR));
                    assert_eq!("Po", langinfo(&m, ffi::ABDAY_2));
                }
            }
        }
    }

    #[test]
    fn locale_with_convert() {
        if let Ok(lf) = LibCLocaleFactory::new("cs_CZ") {
            // only test if the host has cs_CZ (non-unicode) locale (travis boxen don't)
            assert_eq!("ISO-8859-2", lf.langinfo(ffi::CODESET));
            assert_eq!("Út", lf.langinfo(ffi::ABDAY_3));
        }
    }
}
