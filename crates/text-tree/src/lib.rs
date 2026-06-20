//! Persistent text tree for Yulang `str` values.
//!
//! Public string operations count extended grapheme clusters, not bytes or
//! Unicode scalar values. Leaves stay small, while concat/slice/splice share
//! tree structure so large script strings scale without exposing a separate
//! rope type to the language surface.

use std::fmt;
use std::ops::Range;
use std::rc::Rc;

use unicode_segmentation::UnicodeSegmentation;

pub const MAX_LEAF_GRAPHEMES: usize = 64;
pub const MAX_LEAF_BYTES: usize = 64;

#[derive(Debug, Eq)]
pub enum StringTree {
    Empty,
    Leaf(Rc<StringLeaf>),
    Node(Rc<StringNode>),
}

impl Clone for StringTree {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(leaf) => Self::Leaf(leaf.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

impl PartialEq for StringTree {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self.len_bytes() == other.len_bytes()
            && self.to_flat_string() == other.to_flat_string()
    }
}

impl fmt::Display for StringTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => Ok(()),
            Self::Leaf(leaf) => f.write_str(leaf.as_str()),
            Self::Node(node) => {
                write!(f, "{}", node.left)?;
                write!(f, "{}", node.right)
            }
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
            Self::Leaf(leaf) => leaf.len_graphemes,
            Self::Node(node) => node.len_graphemes,
        }
    }

    pub fn len_bytes(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(leaf) => leaf.len_bytes,
            Self::Node(node) => node.len_bytes,
        }
    }

    pub fn line_count(&self) -> usize {
        self.line_breaks() + 1
    }

    pub fn line_start(&self, line: usize) -> Option<usize> {
        if line >= self.line_count() {
            return None;
        }
        self.line_start_unchecked(line)
    }

    pub fn line_range(&self, start: usize, end: usize) -> Option<Range<usize>> {
        if start > end || end > self.line_count() {
            return None;
        }
        let start = self.line_start(start)?;
        let end = if end == self.line_count() {
            self.len()
        } else {
            self.line_start(end)?
        };
        Some(start..end)
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn concat(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Empty, right) => right,
            (left, Self::Empty) => left,
            (Self::Leaf(left), Self::Leaf(right))
                if left.len_graphemes + right.len_graphemes <= MAX_LEAF_GRAPHEMES =>
            {
                let mut merged = String::with_capacity(left.len_bytes + right.len_bytes);
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
                    Self::blacken(join_right(left, left_height, right, right_height))
                } else {
                    Self::blacken(join_left(left, left_height, right, right_height))
                }
            }
        }
    }

    pub fn index(&self, index: usize) -> Option<String> {
        match self {
            Self::Empty => None,
            Self::Leaf(leaf) => leaf.as_str().graphemes(true).nth(index).map(str::to_owned),
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
            Self::Leaf(leaf) => Some(Self::from_str(slice_str_by_graphemes(
                leaf.as_str(),
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
        self.push_to_string(&mut out);
        out
    }

    pub fn push_to_string(&self, out: &mut String) {
        match self {
            Self::Empty => {}
            Self::Leaf(leaf) => out.push_str(leaf.as_str()),
            Self::Node(node) => {
                node.left.push_to_string(out);
                node.right.push_to_string(out);
            }
        }
    }

    pub fn view(&self) -> StringView {
        match self {
            Self::Empty => StringView::Empty,
            Self::Leaf(leaf) => StringView::Leaf(leaf.text.clone()),
            Self::Node(node) => StringView::Node {
                color: node.color,
                len_graphemes: node.len_graphemes,
                len_bytes: node.len_bytes,
                line_breaks: node.line_breaks,
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
            Self::Leaf(Rc::new(StringLeaf::new(value)))
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
            len_graphemes: left.len() + right.len(),
            len_bytes: left.len_bytes() + right.len_bytes(),
            line_breaks: left.line_breaks() + right.line_breaks(),
            left,
            right,
        }))
    }

    fn line_breaks(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(leaf) => leaf.line_breaks,
            Self::Node(node) => node.line_breaks,
        }
    }

    fn line_start_unchecked(&self, line: usize) -> Option<usize> {
        if line == 0 {
            return Some(0);
        }
        match self {
            Self::Empty => None,
            Self::Leaf(leaf) => line_start_in_leaf(leaf.as_str(), line),
            Self::Node(node) => {
                let left_breaks = node.left.line_breaks();
                if line <= left_breaks {
                    node.left.line_start_unchecked(line)
                } else {
                    node.right
                        .line_start_unchecked(line - left_breaks)
                        .map(|start| node.left.len() + start)
                }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringView {
    Empty,
    Leaf(Rc<str>),
    Node {
        color: Color,
        len_graphemes: usize,
        len_bytes: usize,
        line_breaks: usize,
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
pub struct StringLeaf {
    text: Rc<str>,
    len_graphemes: usize,
    len_bytes: usize,
    line_breaks: usize,
}

impl StringLeaf {
    fn new(value: String) -> Self {
        let len_graphemes = grapheme_count(&value);
        let len_bytes = value.len();
        let line_breaks = line_break_count(&value);
        Self {
            text: Rc::from(value.into_boxed_str()),
            len_graphemes,
            len_bytes,
            line_breaks,
        }
    }

    fn as_str(&self) -> &str {
        &self.text
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringNode {
    color: Color,
    len_graphemes: usize,
    len_bytes: usize,
    line_breaks: usize,
    left: StringTree,
    right: StringTree,
}

#[derive(Debug, Eq)]
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

impl PartialEq for BytesTree {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.to_flat_vec() == other.to_flat_vec()
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

impl BytesTree {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn from_bytes(value: &[u8]) -> Self {
        let leaves = chunk_bytes(value)
            .into_iter()
            .map(Self::leaf)
            .collect::<Vec<_>>();
        build_balanced_bytes(leaves)
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
            (left, right) => {
                let mut leaves = Vec::new();
                left.push_leaves(&mut leaves);
                right.push_leaves(&mut leaves);
                build_balanced_bytes(compact_byte_leaves(leaves))
            }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytesNode {
    color: Color,
    len: usize,
    left: BytesTree,
    right: BytesTree,
}

fn join_right(
    left: StringTree,
    left_height: usize,
    right: StringTree,
    right_height: usize,
) -> StringTree {
    match left {
        StringTree::Node(node) => {
            let child_height = left_height - usize::from(node.color == Color::Black);
            let joined = if child_height > right_height {
                join_right(node.right.clone(), child_height, right, right_height)
            } else {
                StringTree::red_node(node.right.clone(), right)
            };
            balance(node.color, node.left.clone(), joined)
        }
        left => StringTree::red_node(left, right),
    }
}

fn join_left(
    left: StringTree,
    left_height: usize,
    right: StringTree,
    right_height: usize,
) -> StringTree {
    match right {
        StringTree::Node(node) => {
            let child_height = right_height - usize::from(node.color == Color::Black);
            let joined = if child_height > left_height {
                join_left(left, left_height, node.left.clone(), child_height)
            } else {
                StringTree::red_node(left, node.left.clone())
            };
            balance(node.color, joined, node.right.clone())
        }
        right => StringTree::red_node(left, right),
    }
}

fn balance(color: Color, left: StringTree, right: StringTree) -> StringTree {
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

fn chunk_str(value: &str) -> Vec<String> {
    let mut chunks = Vec::new();
    let mut start = 0usize;
    let mut current_graphemes = 0usize;
    for (byte_index, _) in value.grapheme_indices(true) {
        if current_graphemes >= MAX_LEAF_GRAPHEMES {
            chunks.push(value[start..byte_index].to_string());
            start = byte_index;
            current_graphemes = 0;
        }
        current_graphemes += 1;
    }
    if start < value.len() {
        chunks.push(value[start..].to_string());
    }
    chunks
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

fn chunk_bytes(value: &[u8]) -> Vec<Vec<u8>> {
    value
        .chunks(MAX_LEAF_BYTES)
        .map(|chunk| chunk.to_vec())
        .collect()
}

fn compact_byte_leaves(leaves: Vec<Vec<u8>>) -> Vec<BytesTree> {
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

fn build_balanced_bytes(mut items: Vec<BytesTree>) -> BytesTree {
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

fn slice_str_by_graphemes(value: &str, start: usize, end: usize) -> Option<&str> {
    let (start_byte, end_byte) = grapheme_range_to_byte_range(value, start, end)?;
    value.get(start_byte..end_byte)
}

pub fn grapheme_count(value: &str) -> usize {
    value.graphemes(true).count()
}

pub fn line_break_count(value: &str) -> usize {
    value
        .graphemes(true)
        .filter(|grapheme| grapheme.chars().any(|ch| ch == '\n'))
        .count()
}

pub fn grapheme_range_to_byte_range(
    value: &str,
    start: usize,
    end: usize,
) -> Option<(usize, usize)> {
    if start > end || end > grapheme_count(value) {
        return None;
    }
    let start_byte = byte_index_for_grapheme(value, start)?;
    let end_byte = byte_index_for_grapheme(value, end)?;
    Some((start_byte, end_byte))
}

fn byte_index_for_grapheme(value: &str, index: usize) -> Option<usize> {
    if index == grapheme_count(value) {
        return Some(value.len());
    }
    value
        .grapheme_indices(true)
        .nth(index)
        .map(|(offset, _)| offset)
}

fn line_start_in_leaf(value: &str, line: usize) -> Option<usize> {
    let mut seen_breaks = 0usize;
    for (index, grapheme) in value.graphemes(true).enumerate() {
        if grapheme.chars().any(|ch| ch == '\n') {
            seen_breaks += 1;
            if seen_breaks == line {
                return Some(index + 1);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{
        BytesTree, BytesView, Color, MAX_LEAF_BYTES, MAX_LEAF_GRAPHEMES, StringTree, StringView,
    };

    #[test]
    fn string_tree_tracks_grapheme_and_byte_len() {
        let text = StringTree::from_str("aあ🙂");

        assert_eq!(text.len(), 3);
        assert_eq!(text.len_bytes(), "aあ🙂".len());
        assert_eq!(text.to_flat_string(), "aあ🙂");
    }

    #[test]
    fn string_tree_tracks_line_starts_as_grapheme_offsets() {
        let text = StringTree::from_str("a👨‍👩‍👧‍👦\nβ\n");

        assert_eq!(text.line_count(), 3);
        assert_eq!(text.line_start(0), Some(0));
        assert_eq!(text.line_start(1), Some(3));
        assert_eq!(text.line_start(2), Some(5));
        assert_eq!(text.line_start(3), None);
        assert_eq!(text.line_range(1, 2), Some(3..5));
        assert_eq!(text.index_range(3, 5).unwrap().to_flat_string(), "β\n");
    }

    #[test]
    fn string_tree_chunks_large_leaves() {
        let source = "x".repeat(MAX_LEAF_GRAPHEMES + 1);
        let text = StringTree::from_str(&source);

        assert!(matches!(text.view(), StringView::Node { .. }));
        assert_eq!(text.to_flat_string(), source);
        assert!(text.is_red_black_well_formed());
    }

    #[test]
    fn string_tree_concat_range_and_splice_use_tree_operations() {
        let text = StringTree::concat(StringTree::from_str("aあ"), StringTree::from_str("🙂z"));

        assert_eq!(text.index(1), Some("あ".to_string()));
        assert_eq!(text.index_range(1, 3).unwrap().to_flat_string(), "あ🙂");
        assert_eq!(
            text.splice(1, 3, StringTree::from_str("bc"))
                .unwrap()
                .to_flat_string(),
            "abcz"
        );
    }

    #[test]
    fn string_tree_indexes_extended_grapheme_clusters() {
        let text = StringTree::from_str("e\u{301}🇯🇵👨‍👩‍👧‍👦!");

        assert_eq!(text.len(), 4);
        assert_eq!(text.index(0), Some("e\u{301}".to_string()));
        assert_eq!(text.index(1), Some("🇯🇵".to_string()));
        assert_eq!(text.index(2), Some("👨‍👩‍👧‍👦".to_string()));
        assert_eq!(
            text.index_range(0, 3).unwrap().to_flat_string(),
            "e\u{301}🇯🇵👨‍👩‍👧‍👦"
        );
    }

    #[test]
    fn string_tree_compares_by_text_not_shape() {
        let left = StringTree::concat(StringTree::from_str("a"), StringTree::from_str("b"));
        let right = StringTree::from_str("ab");

        assert_eq!(left, right);
    }

    #[test]
    fn string_tree_view_reports_node_metadata() {
        let text = StringTree::concat(
            StringTree::from_str(&"a".repeat(MAX_LEAF_GRAPHEMES)),
            StringTree::from_str(&"b".repeat(MAX_LEAF_GRAPHEMES)),
        );
        let StringView::Node {
            color,
            len_graphemes,
            len_bytes,
            line_breaks,
            ..
        } = text.view()
        else {
            panic!("expected node view");
        };

        assert_eq!(color, Color::Black);
        assert_eq!(len_graphemes, MAX_LEAF_GRAPHEMES * 2);
        assert_eq!(len_bytes, MAX_LEAF_GRAPHEMES * 2);
        assert_eq!(line_breaks, 0);
    }

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
    fn bytes_tree_compares_by_content_not_shape() {
        let left = BytesTree::concat(BytesTree::from_bytes(b"a"), BytesTree::from_bytes(b"b"));
        let right = BytesTree::from_bytes(b"ab");

        assert_eq!(left, right);
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
