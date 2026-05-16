use std::rc::Rc;

pub const MAX_LEAF_BYTES: usize = 64;

#[derive(Debug, PartialEq, Eq)]
pub enum BytesTree {
    Empty,
    Leaf(Rc<[u8]>),
    Node(Rc<BytesNode>),
}

impl Clone for BytesTree {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(value) => Self::Leaf(value.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

impl BytesTree {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn from_bytes(value: &[u8]) -> Self {
        let leaves = chunk_bytes(value)
            .into_iter()
            .map(Self::leaf)
            .collect::<Vec<_>>();
        build_balanced(leaves)
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(value) => value.len(),
            Self::Node(node) => node.len,
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn concat(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Empty, right) => right,
            (left, Self::Empty) => left,
            (Self::Leaf(left), Self::Leaf(right)) if left.len() + right.len() <= MAX_LEAF_BYTES => {
                let mut merged = Vec::with_capacity(left.len() + right.len());
                merged.extend_from_slice(&left);
                merged.extend_from_slice(&right);
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

    pub fn index(&self, index: usize) -> Option<u8> {
        match self {
            Self::Empty => None,
            Self::Leaf(value) => value.get(index).copied(),
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
            Self::Leaf(value) => Some(Self::from_bytes(&value[start..end])),
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

    pub fn to_flat_vec(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.len());
        self.push_bytes(&mut out);
        out
    }

    pub fn view(&self) -> BytesView {
        match self {
            Self::Empty => BytesView::Empty,
            Self::Leaf(value) => BytesView::Leaf(value.clone()),
            Self::Node(node) => BytesView::Node {
                color: node.color,
                len: node.len,
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

    fn leaf(value: impl Into<Vec<u8>>) -> Self {
        let value = value.into();
        if value.is_empty() {
            Self::Empty
        } else {
            Self::Leaf(Rc::from(value.into_boxed_slice()))
        }
    }

    fn black_node(left: Self, right: Self) -> Self {
        Self::node(Color::Black, left, right)
    }

    fn red_node(left: Self, right: Self) -> Self {
        Self::node(Color::Red, left, right)
    }

    fn node(color: Color, left: Self, right: Self) -> Self {
        Self::Node(Rc::new(BytesNode {
            color,
            len: left.len() + right.len(),
            left,
            right,
        }))
    }

    fn push_bytes(&self, out: &mut Vec<u8>) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.extend_from_slice(value),
            Self::Node(node) => {
                node.left.push_bytes(out);
                node.right.push_bytes(out);
            }
        }
    }

    fn push_leaves(&self, out: &mut Vec<Vec<u8>>) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.push(value.to_vec()),
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

impl From<&[u8]> for BytesTree {
    fn from(value: &[u8]) -> Self {
        Self::from_bytes(value)
    }
}

impl From<Vec<u8>> for BytesTree {
    fn from(value: Vec<u8>) -> Self {
        Self::from_bytes(&value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BytesView {
    Empty,
    Leaf(Rc<[u8]>),
    Node {
        color: Color,
        len: usize,
        left: BytesTree,
        right: BytesTree,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytesNode {
    pub color: Color,
    pub len: usize,
    pub left: BytesTree,
    pub right: BytesTree,
}

fn chunk_bytes(value: &[u8]) -> Vec<Vec<u8>> {
    value
        .chunks(MAX_LEAF_BYTES)
        .map(|chunk| chunk.to_vec())
        .collect()
}

fn compact_leaves(leaves: Vec<Vec<u8>>) -> Vec<BytesTree> {
    let mut compacted = Vec::new();
    let mut current = Vec::new();
    for leaf in leaves {
        for byte in leaf {
            if current.len() >= MAX_LEAF_BYTES {
                compacted.push(BytesTree::leaf(std::mem::take(&mut current)));
            }
            current.push(byte);
        }
    }
    if !current.is_empty() {
        compacted.push(BytesTree::leaf(current));
    }
    compacted
}

fn build_balanced(mut items: Vec<BytesTree>) -> BytesTree {
    items.retain(|item| !item.is_empty());
    if items.is_empty() {
        return BytesTree::Empty;
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
                    next.push(BytesTree::black_node(first, second));
                    break;
                };
                next.push(BytesTree::black_node(
                    BytesTree::red_node(first, second),
                    third,
                ));
                remaining_triples -= 1;
                continue;
            }
            match pairs.next() {
                Some(second) => next.push(BytesTree::black_node(first, second)),
                None => next.push(first),
            }
        }
        items = next;
    }
    items.pop().unwrap_or(BytesTree::Empty)
}

#[cfg(test)]
mod tests {
    use super::{BytesTree, BytesView, Color, MAX_LEAF_BYTES};

    #[test]
    fn bytes_tree_tracks_length() {
        let value = BytesTree::from_bytes(b"hello");
        assert_eq!(value.len(), 5);
        assert_eq!(value.to_flat_vec(), b"hello".to_vec());
    }

    #[test]
    fn bytes_tree_chunks_large_leaves() {
        let source = vec![b'x'; MAX_LEAF_BYTES + 1];
        let value = BytesTree::from_bytes(&source);

        assert!(matches!(value.view(), BytesView::Node { .. }));
        assert_eq!(value.to_flat_vec(), source);
        assert!(value.is_red_black_well_formed());
    }

    #[test]
    fn bytes_tree_concat_range_and_splice_use_tree_operations() {
        let value = BytesTree::concat(BytesTree::from_bytes(b"ab"), BytesTree::from_bytes(b"cd"));

        assert_eq!(value.index(1), Some(b'b'));
        assert_eq!(
            value.index_range(1, 3).unwrap().to_flat_vec(),
            b"bc".to_vec()
        );
        assert_eq!(
            value
                .splice(1, 3, BytesTree::from_bytes(b"XY"))
                .unwrap()
                .to_flat_vec(),
            b"aXYd".to_vec()
        );
    }

    #[test]
    fn bytes_tree_view_reports_node_metadata() {
        let value = BytesTree::concat(
            BytesTree::from_bytes(&vec![b'a'; MAX_LEAF_BYTES]),
            BytesTree::from_bytes(&vec![b'b'; MAX_LEAF_BYTES]),
        );
        let BytesView::Node { color, len, .. } = value.view() else {
            panic!("expected node view");
        };

        assert_eq!(color, Color::Black);
        assert_eq!(len, MAX_LEAF_BYTES * 2);
    }
}
