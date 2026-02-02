/// Returns the length of the null-terminated string in `s`,
/// not counting the null terminator.
pub fn strlen(s: &[u8]) -> usize {
    let mut i = 0;
    while i < s.len() && s[i] != 0 {
        i += 1;
    }
    i
}

/// Copies the null-terminated string from `src` into `dst`,
/// including the null terminator. `dst` must be large enough.
pub fn strcpy(dst: &mut [u8], src: &[u8]) {
    let mut i = 0;
    loop {
        let c = if i < src.len() { src[i] } else { 0 };
        dst[i] = c;
        if c == 0 {
            break;
        }
        i += 1;
    }
}

/// Copies up to `n` bytes from `src` into `dst`. If the null terminator
/// in `src` is reached before `n` bytes, the remainder of `dst` is
/// zero-padded. If `src` is `n` or more bytes long (before its null
/// terminator), the result in `dst` is *not* null-terminated.
pub fn strncpy(dst: &mut [u8], src: &[u8], n: usize) {
    let mut null_reached = false;
    for i in 0..n {
        if null_reached {
            dst[i] = 0;
        } else if i < src.len() && src[i] != 0 {
            dst[i] = src[i];
        } else {
            null_reached = true;
            dst[i] = 0;
        }
    }
}

/// Lexicographically compares two null-terminated strings.
/// Returns a negative value if `s1 < s2`, zero if equal,
/// or a positive value if `s1 > s2`, matching C `strcmp` semantics.
pub fn strcmp(s1: &[u8], s2: &[u8]) -> i32 {
    let mut i = 0;
    loop {
        let c1 = if i < s1.len() { s1[i] } else { 0 };
        let c2 = if i < s2.len() { s2[i] } else { 0 };
        if c1 != c2 {
            return c1 as i32 - c2 as i32;
        }
        if c1 == 0 {
            return 0;
        }
        i += 1;
    }
}

pub fn strcmp_eq(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) == 0
}

pub fn strcmp_ne(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) != 0
}

pub fn strcmp_lt(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) < 0
}

pub fn strcmp_le(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) <= 0
}

pub fn strcmp_gt(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) > 0
}

pub fn strcmp_ge(s1: &[u8], s2: &[u8]) -> bool {
    strcmp(s1, s2) >= 0
}

/// Compares at most `n` bytes of two null-terminated strings.
pub fn strncmp(s1: &[u8], s2: &[u8], n: usize) -> i32 {
    let mut i = 0;
    while i < n {
        let c1 = if i < s1.len() { s1[i] } else { 0 };
        let c2 = if i < s2.len() { s2[i] } else { 0 };
        if c1 != c2 {
            return c1 as i32 - c2 as i32;
        }
        if c1 == 0 {
            return 0;
        }
        i += 1;
    }
    0
}

/// Returns the length of the initial segment of `s` that consists
/// entirely of bytes found in `accept`. Both are null-terminated.
pub fn strspn(s: &[u8], accept: &[u8]) -> usize {
    let mut count = 0;
    for &c in s {
        if c == 0 {
            break;
        }
        let mut found = false;
        for &a in accept {
            if a == 0 {
                break;
            }
            if c == a {
                found = true;
                break;
            }
        }
        if !found {
            break;
        }
        count += 1;
    }
    count
}

/// Finds the first occurrence of the null-terminated string `needle`
/// in the null-terminated string `haystack`. Returns the byte index
/// of the match, or `None` if not found. An empty needle always
/// matches at index 0.
pub fn strstr_idx(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    let hlen = strlen(haystack);
    let nlen = strlen(needle);
    if nlen == 0 {
        return Some(0);
    }
    if nlen > hlen {
        return None;
    }
    'outer: for i in 0..=(hlen - nlen) {
        for j in 0..nlen {
            if haystack[i + j] != needle[j] {
                continue 'outer;
            }
        }
        return Some(i);
    }
    None
}

/// Appends the null-terminated string `src` onto the end of the
/// null-terminated string in `dst`. `dst` must have enough space
/// for the combined string plus a null terminator.
pub fn strcat(dst: &mut [u8], src: &[u8]) {
    let dst_len = strlen(dst);
    let mut i = 0;
    loop {
        let c = if i < src.len() { src[i] } else { 0 };
        dst[dst_len + i] = c;
        if c == 0 {
            break;
        }
        i += 1;
    }
}

/// Appends at most `n` bytes from `src` onto the end of the
/// null-terminated string in `dst`, then writes a null terminator.
pub fn strncat(dst: &mut [u8], src: &[u8], n: usize) {
    let dst_len = strlen(dst);
    let mut i = 0;
    while i < n {
        if i >= src.len() || src[i] == 0 {
            break;
        }
        dst[dst_len + i] = src[i];
        i += 1;
    }
    dst[dst_len + i] = 0;
}

/// Finds the first occurrence of byte `c` in the null-terminated
/// string `s`. The null terminator is considered part of the string,
/// so searching for `0` will return its index. Returns `None` if
/// `c` is not found.
pub fn strchr_idx(s: &[u8], c: u8) -> Option<usize> {
    for i in 0..s.len() {
        if s[i] == c {
            return Some(i);
        }
        if s[i] == 0 {
            return None;
        }
    }
    None
}

/// Finds the last occurrence of byte `c` in the null-terminated
/// string `s`. The null terminator is considered part of the string.
/// Returns `None` if `c` is not found.
pub fn strrchr_idx(s: &[u8], c: u8) -> Option<usize> {
    let len = strlen(s);
    if c == 0 {
        return Some(len);
    }
    let mut i = len;
    while i > 0 {
        i -= 1;
        if s[i] == c {
            return Some(i);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- strlen --

    #[test]
    fn strlen_basic() {
        assert_eq!(strlen(b"hello\0"), 5);
    }

    #[test]
    fn strlen_empty() {
        assert_eq!(strlen(b"\0"), 0);
    }

    #[test]
    fn strlen_no_null_uses_slice_len() {
        assert_eq!(strlen(b"abc"), 3);
    }

    #[test]
    fn strlen_embedded_null() {
        assert_eq!(strlen(b"ab\0cd\0"), 2);
    }

    // -- strcpy --

    #[test]
    fn strcpy_basic() {
        let mut dst = [0u8; 16];
        strcpy(&mut dst, b"hello\0");
        assert_eq!(&dst[..6], b"hello\0");
    }

    #[test]
    fn strcpy_empty() {
        let mut dst = [0xFFu8; 8];
        strcpy(&mut dst, b"\0");
        assert_eq!(dst[0], 0);
    }

    // -- strncpy --

    #[test]
    fn strncpy_pads_with_nulls() {
        let mut dst = [0xFFu8; 8];
        strncpy(&mut dst, b"hi\0", 8);
        assert_eq!(&dst, b"hi\0\0\0\0\0\0");
    }

    #[test]
    fn strncpy_truncates_without_null() {
        let mut dst = [0xFFu8; 3];
        strncpy(&mut dst, b"hello\0", 3);
        assert_eq!(&dst, b"hel");
    }

    #[test]
    fn strncpy_exact_fit() {
        let mut dst = [0xFFu8; 5];
        strncpy(&mut dst, b"hello\0", 5);
        assert_eq!(&dst, b"hello");
    }

    // -- strcmp --

    #[test]
    fn strcmp_equal() {
        assert_eq!(strcmp(b"abc\0", b"abc\0"), 0);
    }

    #[test]
    fn strcmp_less() {
        assert!(strcmp(b"abc\0", b"abd\0") < 0);
    }

    #[test]
    fn strcmp_greater() {
        assert!(strcmp(b"abd\0", b"abc\0") > 0);
    }

    #[test]
    fn strcmp_prefix() {
        assert!(strcmp(b"ab\0", b"abc\0") < 0);
    }

    #[test]
    fn strcmp_empty() {
        assert_eq!(strcmp(b"\0", b"\0"), 0);
    }

    #[test]
    fn strcmp_eq_bool() {
        assert!(strcmp_eq(b"test\0", b"test\0"));
        assert!(!strcmp_eq(b"test\0", b"tess\0"));
    }

    #[test]
    fn strcmp_ne_bool() {
        assert!(strcmp_ne(b"a\0", b"b\0"));
        assert!(!strcmp_ne(b"a\0", b"a\0"));
    }

    #[test]
    fn strcmp_lt_bool() {
        assert!(strcmp_lt(b"a\0", b"b\0"));
        assert!(!strcmp_lt(b"b\0", b"a\0"));
        assert!(!strcmp_lt(b"a\0", b"a\0"));
    }

    #[test]
    fn strcmp_le_bool() {
        assert!(strcmp_le(b"a\0", b"b\0"));
        assert!(strcmp_le(b"a\0", b"a\0"));
        assert!(!strcmp_le(b"b\0", b"a\0"));
    }

    #[test]
    fn strcmp_gt_bool() {
        assert!(strcmp_gt(b"b\0", b"a\0"));
        assert!(!strcmp_gt(b"a\0", b"b\0"));
        assert!(!strcmp_gt(b"a\0", b"a\0"));
    }

    #[test]
    fn strcmp_ge_bool() {
        assert!(strcmp_ge(b"b\0", b"a\0"));
        assert!(strcmp_ge(b"a\0", b"a\0"));
        assert!(!strcmp_ge(b"a\0", b"b\0"));
    }

    // -- strncmp --

    #[test]
    fn strncmp_equal_within_n() {
        assert_eq!(strncmp(b"abcdef\0", b"abcxyz\0", 3), 0);
    }

    #[test]
    fn strncmp_differs_within_n() {
        assert!(strncmp(b"abcdef\0", b"abcxyz\0", 4) != 0);
    }

    #[test]
    fn strncmp_zero_n() {
        assert_eq!(strncmp(b"a\0", b"b\0", 0), 0);
    }

    #[test]
    fn strncmp_stops_at_null() {
        assert_eq!(strncmp(b"ab\0", b"ab\0", 100), 0);
    }

    // -- strspn --

    #[test]
    fn strspn_basic() {
        assert_eq!(strspn(b"abcdef\0", b"abc\0"), 3);
    }

    #[test]
    fn strspn_none_match() {
        assert_eq!(strspn(b"xyz\0", b"abc\0"), 0);
    }

    #[test]
    fn strspn_all_match() {
        assert_eq!(strspn(b"aabbcc\0", b"abc\0"), 6);
    }

    #[test]
    fn strspn_empty_accept() {
        assert_eq!(strspn(b"abc\0", b"\0"), 0);
    }

    #[test]
    fn strspn_empty_string() {
        assert_eq!(strspn(b"\0", b"abc\0"), 0);
    }

    // -- strstr_idx --

    #[test]
    fn strstr_found() {
        assert_eq!(strstr_idx(b"hello world\0", b"world\0"), Some(6));
    }

    #[test]
    fn strstr_not_found() {
        assert_eq!(strstr_idx(b"hello world\0", b"xyz\0"), None);
    }

    #[test]
    fn strstr_empty_needle() {
        assert_eq!(strstr_idx(b"hello\0", b"\0"), Some(0));
    }

    #[test]
    fn strstr_at_start() {
        assert_eq!(strstr_idx(b"hello\0", b"hel\0"), Some(0));
    }

    #[test]
    fn strstr_at_end() {
        assert_eq!(strstr_idx(b"hello\0", b"llo\0"), Some(2));
    }

    #[test]
    fn strstr_needle_longer() {
        assert_eq!(strstr_idx(b"hi\0", b"hello\0"), None);
    }

    #[test]
    fn strstr_exact_match() {
        assert_eq!(strstr_idx(b"abc\0", b"abc\0"), Some(0));
    }

    // -- strcat --

    #[test]
    fn strcat_basic() {
        let mut buf = [0u8; 16];
        strcpy(&mut buf, b"hello\0");
        strcat(&mut buf, b" world\0");
        assert_eq!(&buf[..12], b"hello world\0");
    }

    #[test]
    fn strcat_to_empty() {
        let mut buf = [0u8; 8];
        buf[0] = 0;
        strcat(&mut buf, b"abc\0");
        assert_eq!(&buf[..4], b"abc\0");
    }

    #[test]
    fn strcat_empty_src() {
        let mut buf = [0u8; 8];
        strcpy(&mut buf, b"abc\0");
        strcat(&mut buf, b"\0");
        assert_eq!(&buf[..4], b"abc\0");
    }

    // -- strncat --

    #[test]
    fn strncat_basic() {
        let mut buf = [0u8; 16];
        strcpy(&mut buf, b"hello\0");
        strncat(&mut buf, b" world\0", 3);
        assert_eq!(&buf[..9], b"hello wo\0");
    }

    #[test]
    fn strncat_n_larger_than_src() {
        let mut buf = [0u8; 16];
        strcpy(&mut buf, b"hello\0");
        strncat(&mut buf, b" !\0", 100);
        assert_eq!(&buf[..8], b"hello !\0");
    }

    #[test]
    fn strncat_zero_n() {
        let mut buf = [0u8; 16];
        strcpy(&mut buf, b"hello\0");
        strncat(&mut buf, b" world\0", 0);
        assert_eq!(&buf[..6], b"hello\0");
    }

    // -- strchr_idx --

    #[test]
    fn strchr_found() {
        assert_eq!(strchr_idx(b"hello\0", b'l'), Some(2));
    }

    #[test]
    fn strchr_not_found() {
        assert_eq!(strchr_idx(b"hello\0", b'z'), None);
    }

    #[test]
    fn strchr_first_byte() {
        assert_eq!(strchr_idx(b"hello\0", b'h'), Some(0));
    }

    #[test]
    fn strchr_null_terminator() {
        assert_eq!(strchr_idx(b"hello\0", 0), Some(5));
    }

    // -- strrchr_idx --

    #[test]
    fn strrchr_found() {
        assert_eq!(strrchr_idx(b"hello\0", b'l'), Some(3));
    }

    #[test]
    fn strrchr_not_found() {
        assert_eq!(strrchr_idx(b"hello\0", b'z'), None);
    }

    #[test]
    fn strrchr_single_occurrence() {
        assert_eq!(strrchr_idx(b"hello\0", b'h'), Some(0));
    }

    #[test]
    fn strrchr_null_terminator() {
        assert_eq!(strrchr_idx(b"hello\0", 0), Some(5));
    }
}
