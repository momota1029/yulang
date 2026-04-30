use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum ListTree<T> {
    Empty,
    Leaf(Rc<T>),
    Node(Rc<ListNode<T>>),
}

impl<T> Clone for ListTree<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Leaf(value) => Self::Leaf(value.clone()),
            Self::Node(node) => Self::Node(node.clone()),
        }
    }
}

impl<T> ListTree<T> {
    pub fn empty() -> Self {
        Self::Empty
    }

    pub fn singleton(value: T) -> Self {
        Self::Leaf(Rc::new(value))
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

    pub fn index(&self, index: usize) -> Option<Rc<T>> {
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
        if start == 0 && end == self.len() {
            return Some(self.clone());
        }
        match self {
            Self::Empty => Some(Self::Empty),
            Self::Leaf(_) => match (start, end) {
                (0, 0) | (1, 1) => Some(Self::Empty),
                (0, 1) => Some(self.clone()),
                _ => None,
            },
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

    pub fn concat(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Empty, right) => right,
            (left, Self::Empty) => left,
            (left, right) => Self::black_node(left, right),
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

    fn black_node(left: Self, right: Self) -> Self {
        Self::node(Color::Black, left, right)
    }

    fn red_node(left: Self, right: Self) -> Self {
        Self::node(Color::Red, left, right)
    }

    fn node(color: Color, left: Self, right: Self) -> Self {
        Self::Node(Rc::new(ListNode {
            color,
            len: left.len() + right.len(),
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
}

impl<T: Clone> ListTree<T> {
    pub fn from_items(items: impl IntoIterator<Item = T>) -> Self {
        let leaves = items.into_iter().map(Self::singleton).collect::<Vec<_>>();
        build_balanced(leaves)
    }

    pub fn to_vec(&self) -> Vec<T> {
        let mut out = Vec::with_capacity(self.len());
        self.push_items(&mut out);
        out
    }

    fn push_items(&self, out: &mut Vec<T>) {
        match self {
            Self::Empty => {}
            Self::Leaf(value) => out.push((**value).clone()),
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
    Leaf(Rc<T>),
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
    pub left: ListTree<T>,
    pub right: ListTree<T>,
}

fn build_balanced<T>(mut items: Vec<ListTree<T>>) -> ListTree<T> {
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
}
