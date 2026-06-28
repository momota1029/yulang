#![forbid(unsafe_code)]

use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum ListTree<T> {
    Empty,
    Leaf(T),
    Node(Rc<ListNode<T>>),
}

impl<T: Clone> Clone for ListTree<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(value) => Self::Leaf(value.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

impl<T: Clone> ListTree<T> {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn singleton(value: T) -> Self {
        Self::Leaf(value)
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Leaf(_) => 1,
            Self::Node(node) => node.len,
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn view(&self) -> ListView<T> {
        match self {
            Self::Empty => ListView::Empty,
            Self::Leaf(value) => ListView::Leaf(value.clone()),
            Self::Node(node) => ListView::Node {
                color: node.color,
                len: node.len,
                left: node.left.clone(),
                right: node.right.clone(),
            },
        }
    }

    pub fn index(&self, index: usize) -> Option<T> {
        match self {
            Self::Empty => None,
            Self::Leaf(value) => (index == 0).then_some(value.clone()),
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
        let (_, suffix) = self.split_at(start)?;
        let (range, _) = suffix.split_at(end - start)?;
        Some(range)
    }

    pub fn splice(&self, start: usize, end: usize, insert: Self) -> Option<Self> {
        if start > end || end > self.len() {
            return None;
        }
        let (prefix, rest) = self.split_at(start)?;
        let (_, suffix) = rest.split_at(end - start)?;
        Some(Self::concat(prefix, Self::concat(insert, suffix)))
    }

    pub fn split_at(&self, index: usize) -> Option<(Self, Self)> {
        if index > self.len() {
            return None;
        }
        Some(self.split_at_unchecked(index))
    }

    pub fn concat(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Empty, right) => right,
            (left, Self::Empty) => left,
            (left, right) => {
                let left_height = left.black_height();
                let right_height = right.black_height();
                if left_height == right_height {
                    Self::black_node(left, right)
                } else if left_height > right_height {
                    Self::blacken(join_right(left, left_height, right, right_height))
                } else {
                    Self::blacken(join_left(left, left_height, right, right_height))
                }
            }
        }
    }

    pub fn black_height(&self) -> usize {
        match self {
            Self::Empty | Self::Leaf(_) => 0,
            Self::Node(node) => node.black_height,
        }
    }

    pub fn is_red_black_well_formed(&self) -> bool {
        self.red_black_status().is_some()
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
        let black_height = left.black_height() + usize::from(color == Color::Black);
        Self::Node(Rc::new(ListNode {
            color,
            len: left.len() + right.len(),
            black_height,
            left,
            right,
        }))
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

    fn split_at_unchecked(&self, index: usize) -> (Self, Self) {
        match self {
            Self::Empty => (Self::Empty, Self::Empty),
            Self::Leaf(_) if index == 0 => (Self::Empty, self.clone()),
            Self::Leaf(_) => (self.clone(), Self::Empty),
            Self::Node(node) => {
                let left_len = node.left.len();
                if index < left_len {
                    let (prefix, left_suffix) = node.left.split_at_unchecked(index);
                    (prefix, Self::concat(left_suffix, node.right.clone()))
                } else if index > left_len {
                    let (right_prefix, suffix) = node.right.split_at_unchecked(index - left_len);
                    (Self::concat(node.left.clone(), right_prefix), suffix)
                } else {
                    (node.left.clone(), node.right.clone())
                }
            }
        }
    }
    pub fn from_items(items: impl IntoIterator<Item = T>) -> Self {
        let leaves = items.into_iter().map(Self::singleton).collect::<Vec<_>>();
        build_balanced(leaves)
    }

    pub fn to_vec(&self) -> Vec<T> {
        let mut out = Vec::with_capacity(self.len());
        self.push_items(&mut out);
        out
    }

    pub fn for_each_ref(&self, f: &mut impl FnMut(&T)) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => f(value),
            Self::Node(node) => {
                node.left.for_each_ref(f);
                node.right.for_each_ref(f);
            }
        }
    }

    fn push_items(&self, out: &mut Vec<T>) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.push(value.clone()),
            Self::Node(node) => {
                node.left.push_items(out);
                node.right.push_items(out);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ListView<T> {
    Empty,
    Leaf(T),
    Node {
        color: Color,
        len: usize,
        left: ListTree<T>,
        right: ListTree<T>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListNode<T> {
    pub color: Color,
    pub len: usize,
    pub black_height: usize,
    pub left: ListTree<T>,
    pub right: ListTree<T>,
}

fn build_balanced<T: Clone>(mut items: Vec<ListTree<T>>) -> ListTree<T> {
    if items.is_empty() {
        return ListTree::Empty;
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
                    next.push(ListTree::black_node(first, second));
                    break;
                };
                next.push(ListTree::black_node(
                    ListTree::red_node(first, second),
                    third,
                ));
                remaining_triples -= 1;
                continue;
            }
            match pairs.next() {
                Some(second) => next.push(ListTree::black_node(first, second)),
                None => next.push(first),
            }
        }
        items = next;
    }
    items.pop().unwrap_or(ListTree::Empty)
}

fn join_right<T: Clone>(
    left: ListTree<T>,
    left_height: usize,
    right: ListTree<T>,
    right_height: usize,
) -> ListTree<T> {
    match left {
        ListTree::Node(node) => {
            let child_height = left_height - usize::from(node.color == Color::Black);
            let joined = if child_height > right_height {
                join_right(node.right.clone(), child_height, right, right_height)
            } else {
                ListTree::red_node(node.right.clone(), right)
            };
            balance(node.color, node.left.clone(), joined)
        }
        left => ListTree::red_node(left, right),
    }
}

fn join_left<T: Clone>(
    left: ListTree<T>,
    left_height: usize,
    right: ListTree<T>,
    right_height: usize,
) -> ListTree<T> {
    match right {
        ListTree::Node(node) => {
            let child_height = right_height - usize::from(node.color == Color::Black);
            let joined = if child_height > left_height {
                join_left(left, left_height, node.left.clone(), child_height)
            } else {
                ListTree::red_node(left, node.left.clone())
            };
            balance(node.color, joined, node.right.clone())
        }
        right => ListTree::red_node(left, right),
    }
}

fn balance<T: Clone>(color: Color, left: ListTree<T>, right: ListTree<T>) -> ListTree<T> {
    if color != Color::Black {
        return ListTree::node(color, left, right);
    }

    if let ListTree::Node(left_node) = &left
        && left_node.color == Color::Red
    {
        if let ListTree::Node(left_left_node) = &left_node.left
            && left_left_node.color == Color::Red
        {
            return ListTree::red_node(
                ListTree::black_node(left_left_node.left.clone(), left_left_node.right.clone()),
                ListTree::black_node(left_node.right.clone(), right),
            );
        }
        if let ListTree::Node(left_right_node) = &left_node.right
            && left_right_node.color == Color::Red
        {
            return ListTree::red_node(
                ListTree::black_node(left_node.left.clone(), left_right_node.left.clone()),
                ListTree::black_node(left_right_node.right.clone(), right),
            );
        }
    }

    if let ListTree::Node(right_node) = &right
        && right_node.color == Color::Red
    {
        if let ListTree::Node(right_left_node) = &right_node.left
            && right_left_node.color == Color::Red
        {
            return ListTree::red_node(
                ListTree::black_node(left, right_left_node.left.clone()),
                ListTree::black_node(right_left_node.right.clone(), right_node.right.clone()),
            );
        }
        if let ListTree::Node(right_right_node) = &right_node.right
            && right_right_node.color == Color::Red
        {
            return ListTree::red_node(
                ListTree::black_node(left, right_node.left.clone()),
                ListTree::black_node(
                    right_right_node.left.clone(),
                    right_right_node.right.clone(),
                ),
            );
        }
    }

    ListTree::black_node(left, right)
}

#[cfg(test)]
mod tests {
    use super::{Color, ListTree, ListView};

    #[test]
    fn list_tree_from_items_forms_red_black_tree() {
        for len in 0..16 {
            let list = ListTree::from_items(0..len);
            assert!(list.is_red_black_well_formed(), "len={len}");
        }
    }

    #[test]
    fn list_tree_concat_preserves_binary_view() {
        let list = ListTree::concat(ListTree::from_items([1, 2]), ListTree::from_items([3, 4]));
        let ListView::Node {
            color,
            len,
            left,
            right,
        } = list.view()
        else {
            panic!("expected node view");
        };

        assert_eq!(color, Color::Black);
        assert_eq!(len, 4);
        assert_eq!(left.to_vec(), vec![1, 2]);
        assert_eq!(right.to_vec(), vec![3, 4]);
    }

    #[test]
    fn list_tree_range_and_splice_avoid_flat_runtime_shape() {
        let list = ListTree::from_items([10, 20, 30, 40]);
        assert_eq!(list.index_range(1, 3).unwrap().to_vec(), vec![20, 30]);
        assert_eq!(
            list.splice(1, 3, ListTree::from_items([99, 98]))
                .unwrap()
                .to_vec(),
            vec![10, 99, 98, 40]
        );
    }

    #[test]
    fn list_tree_split_preserves_red_black_shape() {
        let list = ListTree::from_items(0..4096);

        for index in [0, 1, 17, 2048, 4095, 4096] {
            let (prefix, suffix) = list.split_at(index).unwrap();
            assert!(prefix.is_red_black_well_formed(), "prefix index={index}");
            assert!(suffix.is_red_black_well_formed(), "suffix index={index}");
            assert_eq!(prefix.len(), index);
            assert_eq!(suffix.len(), 4096 - index);
            assert_eq!(ListTree::concat(prefix, suffix).to_vec(), list.to_vec());
        }
    }

    #[test]
    fn list_tree_range_preserves_red_black_shape() {
        let list = ListTree::from_items(0..4096);
        let range = list.index_range(17, 4095).unwrap();

        assert!(range.is_red_black_well_formed());
        assert_eq!(range.len(), 4078);
        assert_eq!(range.index(0), Some(17));
        assert_eq!(range.index(4077), Some(4094));
    }

    #[test]
    fn list_tree_repeated_singleton_concat_stays_balanced() {
        let mut list = ListTree::empty();
        for item in 0..4096 {
            list = ListTree::concat(list, ListTree::singleton(item));
        }

        assert!(list.is_red_black_well_formed());
        assert_eq!(
            list.index_range(4090, 4096).unwrap().to_vec(),
            vec![4090, 4091, 4092, 4093, 4094, 4095]
        );
    }

    #[test]
    fn list_tree_repeated_singleton_prepend_stays_balanced() {
        let mut list = ListTree::empty();
        for item in 0..4096 {
            list = ListTree::concat(ListTree::singleton(item), list);
        }

        assert!(list.is_red_black_well_formed());
        assert_eq!(
            list.index_range(0, 6).unwrap().to_vec(),
            vec![4095, 4094, 4093, 4092, 4091, 4090]
        );
    }
}
