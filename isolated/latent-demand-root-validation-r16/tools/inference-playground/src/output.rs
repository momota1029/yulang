//! One atomic observation budget shared by graphs and diagnostics.
use std::fmt::{self, Write};

pub const BYTE_CAP: usize = 1024 * 1024;
pub const WORK_CAP: usize = 16_384;
pub const CAP_ERROR: &str =
    "tool output cap exceeded: more than 1048576 output bytes or 16384 observation work entries";

pub(crate) struct Output {
    text: String,
    work: usize,
    failed: bool,
}
impl Output {
    pub(crate) fn new() -> Self {
        Self {
            text: String::new(),
            work: 0,
            failed: false,
        }
    }
    pub(crate) fn observe(&mut self, count: usize) -> Result<(), String> {
        if self.failed || count > WORK_CAP - self.work {
            self.failed = true;
            return Err(CAP_ERROR.to_owned());
        }
        self.work += count;
        Ok(())
    }
    pub(crate) fn finish(self) -> Result<String, String> {
        if self.failed {
            Err(CAP_ERROR.to_owned())
        } else {
            Ok(self.text)
        }
    }
}
impl Write for Output {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        if self.failed || value.len() > BYTE_CAP - self.text.len() {
            self.failed = true;
            return Err(fmt::Error);
        }
        let needed = self.text.len() + value.len();
        if needed > self.text.capacity() {
            // Grow geometrically, but request no capacity beyond the byte cap.
            let target = needed
                .max(self.text.capacity().saturating_mul(2))
                .min(BYTE_CAP);
            self.text.reserve_exact(target - self.text.len());
        }
        self.text.push_str(value);
        Ok(())
    }
}
pub(crate) fn cap(_: fmt::Error) -> String {
    CAP_ERROR.to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn byte_boundary_and_failed_publication_are_atomic() {
        let mut output = Output::new();
        output.write_str(&"é".repeat(BYTE_CAP / 2)).unwrap();
        assert_eq!(output.text.len(), BYTE_CAP);
        assert!(output.write_str("x").is_err());
        assert_eq!(output.text.len(), BYTE_CAP);
        assert_eq!(output.finish().unwrap_err(), CAP_ERROR);
        let mut exact = Output::new();
        exact.write_str(&"x".repeat(BYTE_CAP)).unwrap();
        assert_eq!(exact.finish().unwrap().len(), BYTE_CAP);
    }
    #[test]
    fn formatted_report_rejects_without_publishing_a_prefix() {
        let mut output = Output::new();
        output.write_str("syntax diagnostics:\n").unwrap();
        let fragment = "x".repeat(64 * 1024);
        for _ in 0..15 {
            output.observe(1).unwrap();
            writeln!(output, "diagnostic at {fragment}").unwrap();
        }
        assert!(writeln!(output, "diagnostic at {fragment}").is_err());
        assert_eq!(output.finish().unwrap_err(), CAP_ERROR);
    }
    #[test]
    fn multiple_graphs_share_the_aggregate_work_boundary() {
        let mut output = Output::new();
        for _graph in 0..4 {
            output.observe(4096).unwrap();
        }
        assert!(output.observe(1).is_err());
        assert!(output.write_str("withheld").is_err());
        assert_eq!(output.finish().unwrap_err(), CAP_ERROR);
        let mut exact = Output::new();
        exact.observe(WORK_CAP).unwrap();
        assert_eq!(exact.finish().unwrap(), "");
    }
}
