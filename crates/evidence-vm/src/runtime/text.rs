use unicode_segmentation::UnicodeSegmentation;

pub(super) fn grapheme_len(text: &str) -> usize {
    UnicodeSegmentation::graphemes(text, true).count()
}

pub(super) fn string_index(text: &str, index: usize) -> Option<String> {
    UnicodeSegmentation::graphemes(text, true)
        .nth(index)
        .map(str::to_string)
}

pub(super) fn string_index_range(text: &str, start: usize, end: usize) -> Option<String> {
    if start > end {
        return None;
    }
    let len = grapheme_len(text);
    if end > len {
        return None;
    }
    Some(
        UnicodeSegmentation::graphemes(text, true)
            .skip(start)
            .take(end - start)
            .collect(),
    )
}

pub(super) fn string_splice(text: &str, start: usize, end: usize, insert: &str) -> Option<String> {
    let prefix = string_index_range(text, 0, start)?;
    let suffix = string_index_range(text, end, grapheme_len(text))?;
    Some(format!("{prefix}{insert}{suffix}"))
}

pub(super) fn string_line_count(text: &str) -> usize {
    text.chars().filter(|ch| *ch == '\n').count() + 1
}

pub(super) fn string_line_range(text: &str, line: usize) -> Option<(usize, usize)> {
    let line_count = string_line_count(text);
    if line > line_count {
        return None;
    }
    let len = grapheme_len(text);
    if line == line_count {
        return Some((len, len));
    }
    let mut starts = vec![0usize];
    for (index, grapheme) in UnicodeSegmentation::graphemes(text, true).enumerate() {
        if grapheme.contains('\n') {
            starts.push(index + 1);
        }
    }
    let start = *starts.get(line)?;
    let end = starts.get(line + 1).copied().unwrap_or(len);
    Some((start, end))
}
