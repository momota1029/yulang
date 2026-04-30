//! Pos/Neg ノードを連番インデックスで管理するアリーナ。
//! PosId/NegId は u32 なので Copy かつアロケーションなし。
//! &self から alloc できるよう RefCell を使う。

use std::cell::RefCell;

use rustc_hash::FxHashMap;

use crate::ids::{NegId, PosId};
use crate::types::{Neg, Pos};

pub struct TypeArena {
    pos: RefCell<Vec<Pos>>,
    neg: RefCell<Vec<Neg>>,
    pos_index: RefCell<FxHashMap<Pos, PosId>>,
    neg_index: RefCell<FxHashMap<Neg, NegId>>,
    /// Pos::Bot の定数インデックス
    pub bot: PosId,
    /// Neg::Top の定数インデックス
    pub top: NegId,
    /// Pos::Row([], bot) の定数インデックス
    pub empty_pos_row: PosId,
    /// Neg::Row([], top) の定数インデックス
    pub empty_neg_row: NegId,
}

impl Clone for TypeArena {
    fn clone(&self) -> Self {
        Self {
            pos: RefCell::new(self.pos.borrow().clone()),
            neg: RefCell::new(self.neg.borrow().clone()),
            pos_index: RefCell::new(self.pos_index.borrow().clone()),
            neg_index: RefCell::new(self.neg_index.borrow().clone()),
            bot: self.bot,
            top: self.top,
            empty_pos_row: self.empty_pos_row,
            empty_neg_row: self.empty_neg_row,
        }
    }
}

impl PartialEq for TypeArena {
    fn eq(&self, other: &Self) -> bool {
        *self.pos.borrow() == *other.pos.borrow() && *self.neg.borrow() == *other.neg.borrow()
    }
}

impl Eq for TypeArena {}

impl std::fmt::Debug for TypeArena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeArena")
            .field("pos_len", &self.pos.borrow().len())
            .field("neg_len", &self.neg.borrow().len())
            .field("pos_interned", &self.pos_index.borrow().len())
            .field("neg_interned", &self.neg_index.borrow().len())
            .field("bot", &self.bot)
            .field("top", &self.top)
            .field("empty_pos_row", &self.empty_pos_row)
            .field("empty_neg_row", &self.empty_neg_row)
            .finish()
    }
}

impl TypeArena {
    pub fn new() -> Self {
        let mut pos: Vec<Pos> = Vec::new();
        let mut neg: Vec<Neg> = Vec::new();
        let mut pos_index = FxHashMap::default();
        let mut neg_index = FxHashMap::default();

        let bot = PosId(pos.len() as u32);
        let bot_node = Pos::Bot;
        pos.push(bot_node.clone());
        pos_index.insert(bot_node, bot);

        let top = NegId(neg.len() as u32);
        let top_node = Neg::Top;
        neg.push(top_node.clone());
        neg_index.insert(top_node, top);

        let empty_pos_row = PosId(pos.len() as u32);
        let empty_pos_row_node = Pos::Row(vec![], bot);
        pos.push(empty_pos_row_node.clone());
        pos_index.insert(empty_pos_row_node, empty_pos_row);

        let empty_neg_row = NegId(neg.len() as u32);
        let empty_neg_row_node = Neg::Row(vec![], top);
        neg.push(empty_neg_row_node.clone());
        neg_index.insert(empty_neg_row_node, empty_neg_row);

        Self {
            pos: RefCell::new(pos),
            neg: RefCell::new(neg),
            pos_index: RefCell::new(pos_index),
            neg_index: RefCell::new(neg_index),
            bot,
            top,
            empty_pos_row,
            empty_neg_row,
        }
    }

    pub fn alloc_pos(&self, p: Pos) -> PosId {
        if let Some(id) = self.pos_index.borrow().get(&p).copied() {
            return id;
        }
        let mut v = self.pos.borrow_mut();
        let id = PosId(v.len() as u32);
        v.push(p.clone());
        self.pos_index.borrow_mut().insert(p, id);
        id
    }

    pub fn alloc_neg(&self, n: Neg) -> NegId {
        if let Some(id) = self.neg_index.borrow().get(&n).copied() {
            return id;
        }
        let mut v = self.neg.borrow_mut();
        let id = NegId(v.len() as u32);
        v.push(n.clone());
        self.neg_index.borrow_mut().insert(n, id);
        id
    }

    /// Pos ノードをクローンして返す。
    /// PosId を含むバリアントは u32 フィールドしか持たないので安価。
    pub fn get_pos(&self, id: PosId) -> Pos {
        self.pos.borrow()[id.0 as usize].clone()
    }

    /// Neg ノードをクローンして返す。
    pub fn get_neg(&self, id: NegId) -> Neg {
        self.neg.borrow()[id.0 as usize].clone()
    }

    /// 参照返し版（borrow を呼び出し側で保持できる場合）。
    /// 使い方: `let guard = arena.borrow_pos_vec(); let p = &guard[id.0 as usize];`
    pub fn borrow_pos_vec(&self) -> std::cell::Ref<'_, Vec<Pos>> {
        self.pos.borrow()
    }

    pub fn borrow_neg_vec(&self) -> std::cell::Ref<'_, Vec<Neg>> {
        self.neg.borrow()
    }
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::TypeVar;

    #[test]
    fn interns_identical_pos_nodes() {
        let arena = TypeArena::new();
        let left = arena.alloc_pos(Pos::Var(TypeVar(1)));
        let right = arena.alloc_pos(Pos::Var(TypeVar(2)));
        let pair1 = arena.alloc_pos(Pos::Tuple(vec![left, right]));
        let pair2 = arena.alloc_pos(Pos::Tuple(vec![left, right]));
        assert_eq!(pair1, pair2);
    }

    #[test]
    fn interns_identical_neg_nodes() {
        let arena = TypeArena::new();
        let left = arena.alloc_neg(Neg::Var(TypeVar(1)));
        let right = arena.alloc_neg(Neg::Var(TypeVar(2)));
        let row1 = arena.alloc_neg(Neg::Row(vec![left], right));
        let row2 = arena.alloc_neg(Neg::Row(vec![left], right));
        assert_eq!(row1, row2);
    }

    #[test]
    fn reuses_builtin_constants() {
        let arena = TypeArena::new();
        assert_eq!(arena.alloc_pos(Pos::Bot), arena.bot);
        assert_eq!(arena.alloc_neg(Neg::Top), arena.top);
        assert_eq!(
            arena.alloc_pos(Pos::Row(vec![], arena.bot)),
            arena.empty_pos_row
        );
        assert_eq!(
            arena.alloc_neg(Neg::Row(vec![], arena.top)),
            arena.empty_neg_row
        );
    }
}
