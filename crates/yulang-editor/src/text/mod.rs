#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ByteRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Utf16Position {
    pub line: u32,
    pub character: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Utf16Range {
    pub start: Utf16Position,
    pub end: Utf16Position,
}

pub fn subtract_prefix_after_start(range: ByteRange, prefix_len: usize) -> ByteRange {
    if range.start < prefix_len {
        return range;
    }
    ByteRange {
        start: range.start - prefix_len,
        end: range.end.saturating_sub(prefix_len),
    }
}

pub fn subtract_prefix_saturating(range: ByteRange, prefix_len: usize) -> ByteRange {
    ByteRange {
        start: range.start.saturating_sub(prefix_len),
        end: range.end.saturating_sub(prefix_len),
    }
}

pub fn clamp_byte_range_to_len(range: ByteRange, len: usize) -> ByteRange {
    let start = range.start.min(len);
    let end = range.end.min(len).max(start);
    ByteRange { start, end }
}

pub fn utf16_range_for_byte_range(source: &str, range: ByteRange) -> Utf16Range {
    let range = clamp_byte_range_to_source(source, range);
    let line_starts = compute_line_starts(source);
    Utf16Range {
        start: byte_offset_to_utf16_position(source, &line_starts, range.start),
        end: byte_offset_to_utf16_position(source, &line_starts, range.end),
    }
}

pub fn compute_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (index, byte) in source.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(index + 1);
        }
    }
    starts
}

pub fn byte_offset_to_utf16_position(
    source: &str,
    line_starts: &[usize],
    offset: usize,
) -> Utf16Position {
    let line = line_starts
        .partition_point(|start| *start <= offset)
        .saturating_sub(1);
    let line_start = line_starts.get(line).copied().unwrap_or(0);
    Utf16Position {
        line: line as u32,
        character: source[line_start..offset].encode_utf16().count() as u32,
    }
}

pub fn utf16_position_to_byte_offset(source: &str, position: Utf16Position) -> Option<usize> {
    let line_starts = compute_line_starts(source);
    let line_start = *line_starts.get(position.line as usize)?;
    let line_end = line_starts
        .get(position.line as usize + 1)
        .map(|next| next.saturating_sub(1))
        .unwrap_or(source.len());
    let mut utf16_column = 0u32;
    for (relative, ch) in source[line_start..line_end].char_indices() {
        if utf16_column == position.character {
            return Some(line_start + relative);
        }
        let next_column = utf16_column + ch.len_utf16() as u32;
        if position.character < next_column {
            return None;
        }
        utf16_column = next_column;
    }
    (utf16_column == position.character).then_some(line_end)
}

pub fn utf16_range_contains_position(range: Utf16Range, position: Utf16Position) -> bool {
    position_is_at_or_after(position, range.start) && position_is_before(position, range.end)
}

fn clamp_byte_range_to_source(source: &str, range: ByteRange) -> ByteRange {
    let start = clamp_to_char_boundary(source, range.start.min(source.len()));
    let end = clamp_to_char_boundary(source, range.end.min(source.len())).max(start);
    ByteRange { start, end }
}

fn position_is_at_or_after(position: Utf16Position, boundary: Utf16Position) -> bool {
    (position.line, position.character) >= (boundary.line, boundary.character)
}

fn position_is_before(position: Utf16Position, boundary: Utf16Position) -> bool {
    (position.line, position.character) < (boundary.line, boundary.character)
}

fn clamp_to_char_boundary(source: &str, mut offset: usize) -> usize {
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

#[cfg(test)]
mod tests;
