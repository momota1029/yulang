use std::rc::Rc;

pub const MAX_LEAF_CHARS: usize = 64;

#[derive(Debug, PartialEq, Eq)]
pub enum StringTree<S = Rc<str>>
where
    S: StringLeaf,
{
    Empty,
    Leaf(S),
    Node(Rc<StringNode<S>>),
}

impl<S> Clone for StringTree<S>
where
    S: StringLeaf,
{
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(value) => Self::Leaf(value.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

pub trait StringLeaf: Clone + std::fmt::Debug + PartialEq + Eq {
    fn from_string(value: String) -> Self;
    fn as_str(&self) -> &str;
}

impl StringLeaf for Rc<str> {
    fn from_string(value: String) -> Self {
        Rc::from(value.into_boxed_str())
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl StringLeaf for String {
    fn from_string(value: String) -> Self {
        value
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl StringLeaf for Box<str> {
    fn from_string(value: String) -> Self {
        value.into_boxed_str()
    }

    fn as_str(&self) -> &str {
        self
    }
}

impl<S> StringTree<S>
where
    S: StringLeaf,
{
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
            Self::Leaf(value) => value.as_str().chars().count(),
            Self::Node(node) => node.len_chars,
        }
    }

    pub fn len_bytes(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(value) => value.as_str().len(),
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
                if left.as_str().chars().count() + right.as_str().chars().count()
                    <= MAX_LEAF_CHARS =>
            {
                let mut merged = String::with_capacity(left.as_str().len() + right.as_str().len());
                merged.push_str(left.as_str());
                merged.push_str(right.as_str());
                Self::leaf(merged)
            }
            (left, right) if left.black_height() == right.black_height() => {
                Self::black_node(left, right)
            }
            (left, right) => {
                let left_height = left.black_height();
                let right_height = right.black_height();
                if left_height > right_height {
                    Self::blacken(join_right(left, right, right_height))
                } else {
                    Self::blacken(join_left(left, right, left_height))
                }
            }
        }
    }

    pub fn index(&self, index: usize) -> Option<char> {
        match self {
            Self::Empty => None,
            Self::Leaf(value) => value.as_str().chars().nth(index),
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
            Self::Leaf(value) => Some(Self::from_str(slice_str_by_chars(
                value.as_str(),
                start,
                end,
            )?)),
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

    pub fn view(&self) -> StringView<S> {
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
            Self::Leaf(S::from_string(value))
        }
    }

    fn black_node(left: Self, right: Self) -> Self {
        Self::node(Color::Black, left, right)
    }

    fn red_node(left: Self, right: Self) -> Self {
        Self::node(Color::Red, left, right)
    }

    fn blacken(tree: Self) -> Self {
        match tree {
            Self::Node(node) if node.color == Color::Red => {
                Self::black_node(node.left.clone(), node.right.clone())
            }
            tree => tree,
        }
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
            Self::Leaf(value) => out.push_str(value.as_str()),
            Self::Node(node) => {
                node.left.push_str(out);
                node.right.push_str(out);
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

fn join_right<S>(left: StringTree<S>, right: StringTree<S>, right_height: usize) -> StringTree<S>
where
    S: StringLeaf,
{
    match left {
        StringTree::Node(node) if node.right.black_height() > right_height => {
            let joined = join_right(node.right.clone(), right, right_height);
            balance(node.color, node.left.clone(), joined)
        }
        StringTree::Node(node) => {
            let joined = StringTree::red_node(node.right.clone(), right);
            balance(node.color, node.left.clone(), joined)
        }
        left => StringTree::red_node(left, right),
    }
}

fn join_left<S>(left: StringTree<S>, right: StringTree<S>, left_height: usize) -> StringTree<S>
where
    S: StringLeaf,
{
    match right {
        StringTree::Node(node) if node.left.black_height() > left_height => {
            let joined = join_left(left, node.left.clone(), left_height);
            balance(node.color, joined, node.right.clone())
        }
        StringTree::Node(node) => {
            let joined = StringTree::red_node(left, node.left.clone());
            balance(node.color, joined, node.right.clone())
        }
        right => StringTree::red_node(left, right),
    }
}

fn balance<S>(color: Color, left: StringTree<S>, right: StringTree<S>) -> StringTree<S>
where
    S: StringLeaf,
{
    if color != Color::Black {
        return StringTree::node(color, left, right);
    }

    if let StringTree::Node(left_node) = &left
        && left_node.color == Color::Red
    {
        if let StringTree::Node(left_left_node) = &left_node.left
            && left_left_node.color == Color::Red
        {
            return StringTree::red_node(
                StringTree::black_node(left_left_node.left.clone(), left_left_node.right.clone()),
                StringTree::black_node(left_node.right.clone(), right),
            );
        }
        if let StringTree::Node(left_right_node) = &left_node.right
            && left_right_node.color == Color::Red
        {
            return StringTree::red_node(
                StringTree::black_node(left_node.left.clone(), left_right_node.left.clone()),
                StringTree::black_node(left_right_node.right.clone(), right),
            );
        }
    }

    if let StringTree::Node(right_node) = &right
        && right_node.color == Color::Red
    {
        if let StringTree::Node(right_left_node) = &right_node.left
            && right_left_node.color == Color::Red
        {
            return StringTree::red_node(
                StringTree::black_node(left, right_left_node.left.clone()),
                StringTree::black_node(right_left_node.right.clone(), right_node.right.clone()),
            );
        }
        if let StringTree::Node(right_right_node) = &right_node.right
            && right_right_node.color == Color::Red
        {
            return StringTree::red_node(
                StringTree::black_node(left, right_node.left.clone()),
                StringTree::black_node(
                    right_right_node.left.clone(),
                    right_right_node.right.clone(),
                ),
            );
        }
    }

    StringTree::black_node(left, right)
}

impl<S> From<&str> for StringTree<S>
where
    S: StringLeaf,
{
    fn from(value: &str) -> Self {
        Self::from_str(value)
    }
}

impl<S> From<String> for StringTree<S>
where
    S: StringLeaf,
{
    fn from(value: String) -> Self {
        Self::from_str(&value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringView<S = Rc<str>>
where
    S: StringLeaf,
{
    Empty,
    Leaf(S),
    Node {
        color: Color,
        len_chars: usize,
        len_bytes: usize,
        left: StringTree<S>,
        right: StringTree<S>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringNode<S = Rc<str>>
where
    S: StringLeaf,
{
    pub color: Color,
    pub len_chars: usize,
    pub len_bytes: usize,
    pub left: StringTree<S>,
    pub right: StringTree<S>,
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

fn build_balanced<S>(mut items: Vec<StringTree<S>>) -> StringTree<S>
where
    S: StringLeaf,
{
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

    type RuntimeStringTree = StringTree<std::rc::Rc<str>>;

    #[test]
    fn string_tree_tracks_char_and_byte_len() {
        let text = RuntimeStringTree::from_str("aあ🙂");

        assert_eq!(text.len(), 3);
        assert_eq!(text.len_bytes(), "aあ🙂".len());
        assert_eq!(text.to_flat_string(), "aあ🙂");
    }

    #[test]
    fn string_tree_chunks_large_leaves() {
        let source = "x".repeat(MAX_LEAF_CHARS + 1);
        let text = RuntimeStringTree::from_str(&source);

        assert!(matches!(text.view(), StringView::Node { .. }));
        assert_eq!(text.to_flat_string(), source);
        assert!(text.is_red_black_well_formed());
    }

    #[test]
    fn string_tree_concat_range_and_splice_use_tree_operations() {
        let text = RuntimeStringTree::concat(
            RuntimeStringTree::from_str("aあ"),
            RuntimeStringTree::from_str("🙂z"),
        );
        let (StringView::Leaf(_) | StringView::Node { .. }) = text.view() else {
            panic!("expected non-empty text");
        };

        assert_eq!(text.index(1), Some('あ'));
        assert_eq!(text.index_range(1, 3).unwrap().to_flat_string(), "あ🙂");
        assert_eq!(
            text.splice(1, 3, RuntimeStringTree::from_str("bc"))
                .unwrap()
                .to_flat_string(),
            "abcz"
        );
    }

    #[test]
    fn string_tree_view_reports_node_metadata() {
        let text = RuntimeStringTree::concat(
            RuntimeStringTree::from_str(&"a".repeat(MAX_LEAF_CHARS)),
            RuntimeStringTree::from_str(&"b".repeat(MAX_LEAF_CHARS)),
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

    #[test]
    fn string_tree_repeated_singleton_concat_stays_balanced() {
        let mut text = RuntimeStringTree::empty();
        let mut expected = String::new();
        for index in 0..4096 {
            let ch = char::from(b'a' + (index % 26) as u8);
            expected.push(ch);
            text = RuntimeStringTree::concat(text, RuntimeStringTree::from_str(&ch.to_string()));
        }

        assert!(text.is_red_black_well_formed());
        assert_eq!(text.len(), 4096);
        assert_eq!(text.to_flat_string(), expected);
    }

    #[test]
    fn string_tree_repeated_singleton_prepend_stays_balanced() {
        let mut text = RuntimeStringTree::empty();
        let mut expected = String::new();
        for index in 0..4096 {
            let ch = char::from(b'a' + (index % 26) as u8);
            expected.insert(0, ch);
            text = RuntimeStringTree::concat(RuntimeStringTree::from_str(&ch.to_string()), text);
        }

        assert!(text.is_red_black_well_formed());
        assert_eq!(text.len(), 4096);
        assert_eq!(text.to_flat_string(), expected);
    }
}
