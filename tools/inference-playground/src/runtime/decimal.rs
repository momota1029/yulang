//! Signed decimal arithmetic with an explicit multiplication step boundary.

fn parts(value: &str) -> Option<(bool, &str)> {
    let (negative, digits) = value.strip_prefix('-').map_or((false, value), |digits| (true, digits));
    if digits.is_empty() || !digits.bytes().all(|digit| digit.is_ascii_digit()) { return None; }
    let digits = digits.trim_start_matches('0');
    Some(if digits.is_empty() { (false, "0") } else { (negative, digits) })
}

pub(super) fn negate(value: &str) -> Option<String> {
    let (negative, digits) = parts(value)?;
    let sign = !negative && digits != "0";
    let mut output = String::new();
    output.try_reserve_exact(digits.len().checked_add(usize::from(sign))?).ok()?;
    if sign { output.push('-'); }
    output.push_str(digits);
    Some(output)
}

/// One `advance` performs at most one base-10 digit product. Arguments and the
/// accumulator are private; a caller budget can pause without publishing them.
pub(super) struct Product {
    left: Vec<u8>,
    right: Vec<u8>,
    digits: Vec<u8>,
    negative: bool,
    row: usize,
    column: usize,
    carry: u8,
}

impl Product {
    pub(super) fn new(left: &str, right: &str) -> Option<Self> {
        fn magnitude(digits: &str) -> Option<Vec<u8>> {
            let mut result = Vec::new();
            result.try_reserve_exact(digits.len()).ok()?;
            result.extend(digits.bytes().rev().map(|digit| digit - b'0'));
            Some(result)
        }
        let (ln, left) = parts(left)?;
        let (rn, right) = parts(right)?;
        let zero = left == "0" || right == "0";
        let (left, right) = if zero { ("0", "0") } else { (left, right) };
        let width = left.len().checked_add(right.len())?;
        let mut digits = Vec::new();
        digits.try_reserve_exact(width).ok()?;
        digits.resize(width, 0);
        Some(Self { left: magnitude(left)?, right: magnitude(right)?, digits,
            negative: !zero && ln != rn, row: usize::from(zero), column: 0, carry: 0 })
    }

    pub(super) fn advance(&mut self) -> bool {
        if self.row == self.left.len() { return true; }
        let index = self.row + self.column;
        // Each digit and carry is <= 9, so sum <= 99 fits in u8.
        let sum = self.digits[index] + self.left[self.row] * self.right[self.column] + self.carry;
        self.digits[index] = sum % 10;
        self.carry = sum / 10;
        self.column += 1;
        if self.column == self.right.len() {
            // Earlier rows cannot have reached this next high digit.
            self.digits[self.row + self.right.len()] = self.carry;
            self.row += 1;
            self.column = 0;
            self.carry = 0;
        }
        self.row == self.left.len()
    }

    pub(super) fn finish(mut self) -> Option<String> {
        if self.row != self.left.len() { return None; }
        while self.digits.len() > 1 && self.digits.last() == Some(&0) { self.digits.pop(); }
        self.digits.reverse();
        for digit in &mut self.digits { *digit += b'0'; }
        if self.negative {
            self.digits.try_reserve(1).ok()?;
            self.digits.insert(0, b'-');
        }
        String::from_utf8(self.digits).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_product_matches_integer_arithmetic_and_normalizes_signs() {
        for left in -30i64..=30 {
            for right in -30i64..=30 {
                let mut product = Product::new(&left.to_string(), &right.to_string()).unwrap();
                while !product.advance() {}
                assert_eq!(product.finish().unwrap(), (left * right).to_string());
            }
        }
        for (left, right, expected) in [
            ("-000", "123456789", "0"), ("-00012", "-034", "408"),
            ("12345678901234567890", "12345678901234567890", "152415787532388367501905199875019052100"),
        ] {
            let mut product = Product::new(left, right).unwrap();
            while !product.advance() {}
            assert_eq!(product.finish().unwrap(), expected);
        }
    }

    #[test]
    fn decimal_product_keeps_partial_results_private_and_has_bounded_steps() {
        assert!(Product::new("12", "34").unwrap().finish().is_none());
        let mut product = Product::new("12", "34").unwrap();
        for _ in 0..3 { assert!(!product.advance()); }
        assert!(product.advance());
        assert_eq!(product.finish().unwrap(), "408");
        for invalid in ["", "-", "1x", "+1", "--2"] {
            assert!(Product::new(invalid, "1").is_none());
            assert!(negate(invalid).is_none());
        }
        assert_eq!(negate("-00012").as_deref(), Some("12"));
        assert_eq!(negate("00012").as_deref(), Some("-12"));
        assert_eq!(negate("-0").as_deref(), Some("0"));
    }
}
