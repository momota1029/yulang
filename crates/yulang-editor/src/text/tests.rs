use super::*;

#[test]
fn prefix_subtraction_modes_keep_current_callers_distinct() {
    let range = ByteRange { start: 5, end: 15 };

    assert_eq!(subtract_prefix_after_start(range, 10), range);
    assert_eq!(
        subtract_prefix_saturating(range, 10),
        ByteRange { start: 0, end: 5 }
    );

    let after_prefix = ByteRange { start: 12, end: 15 };
    assert_eq!(
        subtract_prefix_after_start(after_prefix, 10),
        ByteRange { start: 2, end: 5 }
    );
    assert_eq!(
        subtract_prefix_saturating(after_prefix, 10),
        ByteRange { start: 2, end: 5 }
    );
}

#[test]
fn byte_range_clamping_preserves_byte_offset_semantics() {
    assert_eq!(
        clamp_byte_range_to_len(ByteRange { start: 8, end: 4 }, 10),
        ByteRange { start: 8, end: 8 }
    );
    assert_eq!(
        clamp_byte_range_to_len(ByteRange { start: 8, end: 12 }, 10),
        ByteRange { start: 8, end: 10 }
    );
}

#[test]
fn utf16_range_for_byte_range_uses_utf16_columns() {
    let source = "my x = \"💡\"\nmy y: bool = 1\n";
    let start = source.find("y:").unwrap();

    assert_eq!(
        utf16_range_for_byte_range(
            source,
            ByteRange {
                start,
                end: start + 1
            }
        ),
        Utf16Range {
            start: Utf16Position {
                line: 1,
                character: 3
            },
            end: Utf16Position {
                line: 1,
                character: 4
            }
        }
    );
}

#[test]
fn utf16_range_for_byte_range_clamps_to_char_boundaries() {
    let source = "💡x";

    assert_eq!(
        utf16_range_for_byte_range(source, ByteRange { start: 1, end: 5 }),
        Utf16Range {
            start: Utf16Position {
                line: 0,
                character: 0
            },
            end: Utf16Position {
                line: 0,
                character: 3
            }
        }
    );
}

#[test]
fn utf16_position_to_byte_offset_rejects_split_surrogate() {
    let source = "💡x\n";

    assert_eq!(
        utf16_position_to_byte_offset(
            source,
            Utf16Position {
                line: 0,
                character: 2
            }
        ),
        Some("💡".len())
    );
    assert_eq!(
        utf16_position_to_byte_offset(
            source,
            Utf16Position {
                line: 0,
                character: 1
            }
        ),
        None
    );
}
