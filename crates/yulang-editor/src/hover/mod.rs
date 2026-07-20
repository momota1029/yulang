use crate::text::{Utf16Position, Utf16Range, utf16_range_contains_position};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticHoverTarget {
    pub range: Utf16Range,
    pub related: Vec<DiagnosticHoverRelatedTarget>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiagnosticHoverRelatedTarget {
    pub related_index: usize,
    pub range: Utf16Range,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiagnosticHoverSelection {
    pub diagnostic_index: usize,
    pub related_index: Option<usize>,
    pub range: Utf16Range,
}

pub fn select_diagnostic_hover(
    targets: &[DiagnosticHoverTarget],
    position: Utf16Position,
) -> Option<DiagnosticHoverSelection> {
    targets
        .iter()
        .enumerate()
        .find_map(|(diagnostic_index, target)| {
            if utf16_range_contains_position(target.range, position) {
                return Some(DiagnosticHoverSelection {
                    diagnostic_index,
                    related_index: None,
                    range: target.range,
                });
            }
            target.related.iter().find_map(|related| {
                utf16_range_contains_position(related.range, position).then_some(
                    DiagnosticHoverSelection {
                        diagnostic_index,
                        related_index: Some(related.related_index),
                        range: related.range,
                    },
                )
            })
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pos(character: u32) -> Utf16Position {
        Utf16Position { line: 0, character }
    }

    fn range(start: u32, end: u32) -> Utf16Range {
        Utf16Range {
            start: pos(start),
            end: pos(end),
        }
    }

    #[test]
    fn selects_main_range_before_related_ranges() {
        let targets = vec![DiagnosticHoverTarget {
            range: range(2, 4),
            related: vec![DiagnosticHoverRelatedTarget {
                related_index: 0,
                range: range(4, 8),
            }],
        }];

        assert_eq!(
            select_diagnostic_hover(&targets, pos(2)),
            Some(DiagnosticHoverSelection {
                diagnostic_index: 0,
                related_index: None,
                range: range(2, 4)
            })
        );
    }

    #[test]
    fn selects_related_range_when_main_range_does_not_contain_position() {
        let targets = vec![DiagnosticHoverTarget {
            range: range(2, 4),
            related: vec![DiagnosticHoverRelatedTarget {
                related_index: 7,
                range: range(4, 8),
            }],
        }];

        assert_eq!(
            select_diagnostic_hover(&targets, pos(5)),
            Some(DiagnosticHoverSelection {
                diagnostic_index: 0,
                related_index: Some(7),
                range: range(4, 8)
            })
        );
    }
}
