/// Canonical decimal spelling preserves arbitrary precision without choosing a
/// machine integer range. Arithmetic is outside this evaluator's current gate.
pub(super) fn integer(text: &str) -> Option<Box<str>> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let digits = text.trim_start_matches('0');
    Some(if digits.is_empty() { "0" } else { digits }.into())
}

/// Decode only a spelling already admitted by source lowering. Unknown single
/// escape targets drop the slash, matching the frozen source literal owner.
pub(super) fn string(text: &str) -> Option<Box<str>> {
    let quotes = text.chars().take_while(|ch| *ch == '"').count();
    let inner = if quotes >= 3 {
        let delimiter = &text[..quotes];
        text.strip_prefix(delimiter)?.strip_suffix(delimiter)?
    } else {
        text.strip_prefix('"')?.strip_suffix('"')?
    };
    let mut result = String::new();
    let mut chars = inner.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            result.push(ch);
            continue;
        }
        let escaped = chars.next()?;
        match escaped {
            'n' => result.push('\n'),
            'r' => result.push('\r'),
            't' => result.push('\t'),
            '0' => result.push('\0'),
            'u' if chars.peek() == Some(&'{') => {
                chars.next();
                let mut scalar = Some(0u32);
                let mut digits = 0usize;
                loop {
                    let digit = chars.next()?;
                    if digit == '}' {
                        break;
                    }
                    let digit = digit.to_digit(16)?;
                    scalar = scalar.and_then(|value| value.checked_mul(16)?.checked_add(digit));
                    digits += 1;
                }
                if digits == 0 {
                    return None;
                }
                result.push(scalar.and_then(char::from_u32).unwrap_or('\u{fffd}'));
            }
            target => result.push(target),
        }
    }
    Some(result.into_boxed_str())
}

#[cfg(test)]
mod tests {
    use super::string;

    #[test]
    fn heredoc_delimiter_borrow_preserves_decoding() {
        for quote_count in [3, 4, 8] {
            let delimiter = "\"".repeat(quote_count);
            let source = format!("{delimiter}猫\\n{delimiter}");
            assert_eq!(string(&source).as_deref(), Some("猫\n"));
        }

        let delimiter = "\"".repeat(3);
        let insufficient_closer = format!("{delimiter}猫\\n\"\"");
        assert_eq!(string(&insufficient_closer), None);
        assert_eq!(string("\"\"").as_deref(), Some(""));
    }
}
