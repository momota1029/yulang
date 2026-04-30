use std::rc::Rc;

pub const MAX_LEAF_CHARS: usize = 64;

#[derive(Debug, PartialEq, Eq)]
pub enum StringTree {
    Empty,
    Leaf(Rc<str>),
    Node(Rc<StringNode>),
}

impl Clone for StringTree {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(value) => Self::Leaf(value.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

impl StringTree {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn from_str(value: &str) -> Self {
        let leaves = chunk_str(value)
            .into_iter()
            .map(Self::leaf)
            .collect::<Vec<_>>();
        build_balanced(leaves)
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(value) => value.chars().count(),
            Self::Node(node) => node.len_chars,
        }
    }

    pub fn len_bytes(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(value) => value.len(),
            Self::Node(node) => node.len_bytes,
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn concat(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Empty, right) => right,
            (left, Self::Empty) => left,
            (Self::Leaf(left), Self::Leaf(right))
                if left.chars().count() + right.chars().count() <= MAX_LEAF_CHARS =>
            {
                let mut merged = String::with_capacity(left.len() + right.len());
                merged.push_str(&left);
                merged.push_str(&right);
                Self::leaf(merged)
            }
            (left, right) if left.black_height() == right.black_height() => {
                Self::black_node(left, right)
            }
            (left, right) => build_balanced({
                let mut leaves = Vec::new();
                left.push_leaves(&mut leaves);
                right.push_leaves(&mut leaves);
                compact_leaves(leaves)
            }),
        }
    }

    pub fn index(&self, index: usize) -> Option<char> {
        match self {
            Self::Empty => None,
            Self::Leaf(value) => value.chars().nth(index),
            Self::Node(node) => {
                let left_len = node.left.len();
                if index < left_len {
                    node.left.index(index)
                } else {
                    node.right.index(index - left_len)
                }
            }
        }
    }

    pub fn index_range(&self, start: usize, end: usize) -> Option<Self> {
        if start > end || end > self.len() {
            return None;
        }
        if start == 0 && end == self.len() {
            return Some(self.clone());
        }
        match self {
            Self::Empty => Some(Self::Empty),
            Self::Leaf(value) => Some(Self::from_str(slice_str_by_chars(value, start, end)?)),
            Self::Node(node) => {
                let left_len = node.left.len();
                if end <= left_len {
                    node.left.index_range(start, end)
                } else if start >= left_len {
                    node.right.index_range(start - left_len, end - left_len)
                } else {
                    let left = node.left.index_range(start, left_len)?;
                    let right = node.right.index_range(0, end - left_len)?;
                    Some(Self::concat(left, right))
                }
            }
        }
    }

    pub fn splice(&self, start: usize, end: usize, insert: Self) -> Option<Self> {
        if start > end || end > self.len() {
            return None;
        }
        let prefix = self.index_range(0, start)?;
        let suffix = self.index_range(end, self.len())?;
        Some(Self::concat(prefix, Self::concat(insert, suffix)))
    }

    pub fn to_flat_string(&self) -> String {
        let mut out = String::with_capacity(self.len_bytes());
        self.push_str(&mut out);
        out
    }

    pub fn view(&self) -> StringView {
        match self {
            Self::Empty => StringView::Empty,
            Self::Leaf(value) => StringView::Leaf(value.clone()),
            Self::Node(node) => StringView::Node {
                color: node.color,
                len_chars: node.len_chars,
                len_bytes: node.len_bytes,
                left: node.left.clone(),
                right: node.right.clone(),
            },
        }
    }

    pub fn black_height(&self) -> usize {
        match self {
            Self::Empty | Self::Leaf(_) => 0,
            Self::Node(node) => {
                let child_height = node.left.black_height();
                child_height + usize::from(node.color == Color::Black)
            }
        }
    }

    pub fn is_red_black_well_formed(&self) -> bool {
        self.red_black_status().is_some()
    }

    fn leaf(value: impl Into<String>) -> Self {
        let value = value.into();
        if value.is_empty() {
            Self::Empty
        } else {
            Self::Leaf(Rc::from(value.into_boxed_str()))
        }
    }

    fn black_node(left: Self, right: Self) -> Self {
        Self::node(Color::Black, left, right)
    }

    fn red_node(left: Self, right: Self) -> Self {
        Self::node(Color::Red, left, right)
    }

    fn node(color: Color, left: Self, right: Self) -> Self {
        Self::Node(Rc::new(StringNode {
            color,
            len_chars: left.len() + right.len(),
            len_bytes: left.len_bytes() + right.len_bytes(),
            left,
            right,
        }))
    }

    fn push_str(&self, out: &mut String) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.push_str(value),
            Self::Node(node) => {
                node.left.push_str(out);
                node.right.push_str(out);
            }
        }
    }

    fn push_leaves(&self, out: &mut Vec<String>) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.push(value.to_string()),
            Self::Node(node) => {
                node.left.push_leaves(out);
                node.right.push_leaves(out);
            }
        }
    }

    fn red_black_status(&self) -> Option<usize> {
        match self {
            Self::Empty | Self::Leaf(_) => Some(0),
            Self::Node(node) => {
                let left = node.left.red_black_status()?;
                let right = node.right.red_black_status()?;
                if left != right {
                    return None;
                }
                if node.color == Color::Red
                    && (node.left.node_color() == Some(Color::Red)
                        || node.right.node_color() == Some(Color::Red))
                {
                    return None;
                }
                Some(left + usize::from(node.color == Color::Black))
            }
        }
    }

    fn node_color(&self) -> Option<Color> {
        match self {
            Self::Node(node) => Some(node.color),
            _ => None,
        }
    }
}

impl From<&str> for StringTree {
    fn from(value: &str) -> Self {
        Self::from_str(value)
    }
}

impl From<String> for StringTree {
    fn from(value: String) -> Self {
        Self::from_str(&value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringView {
    Empty,
    Leaf(Rc<str>),
    Node {
        color: Color,
        len_chars: usize,
        len_bytes: usize,
        left: StringTree,
        right: StringTree,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringNode {
    pub color: Color,
    pub len_chars: usize,
    pub len_bytes: usize,
    pub left: StringTree,
    pub right: StringTree,
}

fn chunk_str(value: &str) -> Vec<String> {
    let mut chunks = Vec::new();
    let mut current = String::new();
    let mut current_chars = 0usize;
    for ch in value.chars() {
        if current_chars >= MAX_LEAF_CHARS {
            chunks.push(std::mem::take(&mut current));
            current_chars = 0;
        }
        current.push(ch);
        current_chars += 1;
    }
    if !current.is_empty() {
        chunks.push(current);
    }
    chunks
}

fn compact_leaves(leaves: Vec<String>) -> Vec<StringTree> {
    let mut compacted = Vec::new();
    let mut current = String::new();
    let mut current_chars = 0usize;
    for leaf in leaves {
        for ch in leaf.chars() {
            if current_chars >= MAX_LEAF_CHARS {
                compacted.push(StringTree::leaf(std::mem::take(&mut current)));
                current_chars = 0;
            }
            current.push(ch);
            current_chars += 1;
        }
    }
    if !current.is_empty() {
        compacted.push(StringTree::leaf(current));
    }
    compacted
}

fn build_balanced(mut items: Vec<StringTree>) -> StringTree {
    items.retain(|item| !item.is_empty());
    if items.is_empty() {
        return StringTree::Empty;
    }
    while items.len() > 1 {
        let count = items.len();
        let triple_count = if count % 2 == 1 && count >= 3 { 1 } else { 0 };
        let mut next = Vec::with_capacity(items.len().div_ceil(2));
        let mut pairs = items.into_iter();
        let mut remaining_triples = triple_count;
        while let Some(first) = pairs.next() {
            if remaining_triples > 0 {
                let Some(second) = pairs.next() else {
                    next.push(first);
                    break;
                };
                let Some(third) = pairs.next() else {
                    next.push(StringTree::black_node(first, second));
                    break;
                };
                next.push(StringTree::black_node(
                    StringTree::red_node(first, second),
                    third,
                ));
                remaining_triples -= 1;
                continue;
            }
            match pairs.next() {
                Some(second) => next.push(StringTree::black_node(first, second)),
                None => next.push(first),
            }
        }
        items = next;
    }
    items.pop().unwrap_or(StringTree::Empty)
}

fn slice_str_by_chars(value: &str, start: usize, end: usize) -> Option<&str> {
    if start > end {
        return None;
    }
    let start_byte = byte_index_for_char(value, start)?;
    let end_byte = byte_index_for_char(value, end)?;
    value.get(start_byte..end_byte)
}

fn byte_index_for_char(value: &str, index: usize) -> Option<usize> {
    if index == value.chars().count() {
        return Some(value.len());
    }
    value.char_indices().nth(index).map(|(offset, _)| offset)
}

#[cfg(test)]
mod tests {
    use super::{Color, MAX_LEAF_CHARS, StringTree, StringView};

    #[test]
    fn string_tree_tracks_char_and_byte_len() {
        let text = StringTree::from_str("aあ🙂");

        assert_eq!(text.len(), 3);
        assert_eq!(text.len_bytes(), "aあ🙂".len());
        assert_eq!(text.to_flat_string(), "aあ🙂");
    }

    #[test]
    fn string_tree_chunks_large_leaves() {
        let source = "x".repeat(MAX_LEAF_CHARS + 1);
        let text = StringTree::from_str(&source);

        assert!(matches!(text.view(), StringView::Node { .. }));
        assert_eq!(text.to_flat_string(), source);
        assert!(text.is_red_black_well_formed());
    }

    #[test]
    fn string_tree_concat_range_and_splice_use_tree_operations() {
        let text = StringTree::concat(StringTree::from_str("aあ"), StringTree::from_str("🙂z"));
        let (StringView::Leaf(_) | StringView::Node { .. }) = text.view() else {
            panic!("expected non-empty text");
        };

        assert_eq!(text.index(1), Some('あ'));
        assert_eq!(text.index_range(1, 3).unwrap().to_flat_string(), "あ🙂");
        assert_eq!(
            text.splice(1, 3, StringTree::from_str("bc"))
                .unwrap()
                .to_flat_string(),
            "abcz"
        );
    }

    #[test]
    fn string_tree_view_reports_node_metadata() {
        let text = StringTree::concat(
            StringTree::from_str(&"a".repeat(MAX_LEAF_CHARS)),
            StringTree::from_str(&"b".repeat(MAX_LEAF_CHARS)),
        );
        let StringView::Node {
            color,
            len_chars,
            len_bytes,
            ..
        } = text.view()
        else {
            panic!("expected node view");
        };

        assert_eq!(color, Color::Black);
        assert_eq!(len_chars, MAX_LEAF_CHARS * 2);
        assert_eq!(len_bytes, MAX_LEAF_CHARS * 2);
    }
}
