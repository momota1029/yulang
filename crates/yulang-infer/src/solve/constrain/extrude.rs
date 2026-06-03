use rustc_hash::FxHashSet;

use super::Infer;
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{EffectAtom, Neg, Pos};

impl Infer {
    /// Simple-sub の extrusion（代入版）。
    ///
    /// 論文 (Fig.7) の extrude はコピーで「level を下げた近似グラフ」を作る。その目的は
    /// (1) level を下げること、(2) let 多相の instantiation 独立性を保つこと、の2つ。
    /// yulang は (2) を SCC + frozen scheme の instantiate で別に実装済みなので、
    /// extrude に残る役割は (1) だけ。新変数・新ノードを作らず、辿り着いた型変数を
    /// 直接 target level へ「老化」させる（＝代入）。型グラフは不変なので返り値は入力 id。
    /// コピーしないため、コピー由来の変数増殖（compact の Intersection 無限ネスト）も起きない。
    pub fn extrude_pos(&self, pos: PosId, target_lvl: u32) -> PosId {
        if self.max_level_pos(pos) <= target_lvl {
            return pos;
        }
        let mut ctx = ExtrudeCtx::new(target_lvl);
        self.extrude_pos_id(pos, &mut ctx);
        pos
    }

    pub fn extrude_neg(&self, neg: NegId, target_lvl: u32) -> NegId {
        if self.max_level_neg(neg) <= target_lvl {
            return neg;
        }
        let mut ctx = ExtrudeCtx::new(target_lvl);
        self.extrude_neg_id(neg, &mut ctx);
        neg
    }

    fn extrude_pos_id(&self, id: PosId, ctx: &mut ExtrudeCtx) {
        if self.max_level_pos(id) <= ctx.target_lvl {
            return;
        }
        match self.arena.get_pos(id) {
            Pos::Bot => {}
            Pos::Var(tv) | Pos::Raw(tv) => self.extrude_type_var(tv, ctx),
            Pos::Atom(atom) => self.extrude_effect_atom(&atom, ctx),
            Pos::Forall(_, body) => self.extrude_pos_id(body, ctx),
            Pos::Con(_, args) => {
                for (pos, neg) in args {
                    self.extrude_pos_id(pos, ctx);
                    self.extrude_neg_id(neg, ctx);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neg_id(arg, ctx);
                self.extrude_neg_id(arg_eff, ctx);
                self.extrude_pos_id(ret_eff, ctx);
                self.extrude_pos_id(ret, ctx);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
                self.extrude_pos_id(tail, ctx);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.extrude_pos_id(tail, ctx);
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_pos_id(payload, ctx);
                    }
                }
            }
            Pos::Tuple(items) => {
                for item in items {
                    self.extrude_pos_id(item, ctx);
                }
            }
            Pos::Row(items, tail) => {
                for item in items {
                    self.extrude_pos_id(item, ctx);
                }
                self.extrude_pos_id(tail, ctx);
            }
            Pos::Union(left, right) => {
                self.extrude_pos_id(left, ctx);
                self.extrude_pos_id(right, ctx);
            }
        }
    }

    fn extrude_neg_id(&self, id: NegId, ctx: &mut ExtrudeCtx) {
        if self.max_level_neg(id) <= ctx.target_lvl {
            return;
        }
        match self.arena.get_neg(id) {
            Neg::Top => {}
            Neg::Var(tv) => self.extrude_type_var(tv, ctx),
            Neg::Atom(atom) => self.extrude_effect_atom(&atom, ctx),
            Neg::Forall(_, body) => self.extrude_neg_id(body, ctx),
            Neg::Con(_, args) => {
                for (pos, neg) in args {
                    self.extrude_pos_id(pos, ctx);
                    self.extrude_neg_id(neg, ctx);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_pos_id(arg, ctx);
                self.extrude_pos_id(arg_eff, ctx);
                self.extrude_neg_id(ret_eff, ctx);
                self.extrude_neg_id(ret, ctx);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.extrude_neg_id(field.value, ctx);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neg_id(payload, ctx);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
                self.extrude_neg_id(tail, ctx);
            }
            Neg::Intersection(left, right) => {
                self.extrude_neg_id(left, ctx);
                self.extrude_neg_id(right, ctx);
            }
        }
    }

    /// 型変数を target level へ代入老化する（新変数は作らない）。
    /// bounds（lower / upper / compact）も level 不変条件を保つため再帰的に老化する。
    /// bounds はサイクルを持ちうるので visited で多重訪問を止める（論文の cache c に相当）。
    fn extrude_type_var(&self, tv: TypeVar, ctx: &mut ExtrudeCtx) {
        if self.level_of(tv) <= ctx.target_lvl {
            return;
        }
        if !ctx.visited.insert(tv) {
            return;
        }
        self.bump_extrude_counter(tv, ctx.target_lvl);
        self.register_level(tv, ctx.target_lvl);
        for lower in self.lower_refs_of(tv) {
            self.extrude_pos_id(lower, ctx);
        }
        for upper in self.upper_refs_of(tv) {
            self.extrude_neg_id(upper, ctx);
        }
        for instance in self.compact_lower_instances_of(tv) {
            let lower = self.materialize_compact_lower_instance(&instance);
            self.extrude_pos_id(lower, ctx);
        }
    }

    fn extrude_effect_atom(&self, atom: &EffectAtom, ctx: &mut ExtrudeCtx) {
        for (pos, neg) in &atom.args {
            self.extrude_type_var(*pos, ctx);
            self.extrude_type_var(*neg, ctx);
        }
    }

    fn max_level_pos(&self, id: PosId) -> u32 {
        if let Some(level) = self.pos_max_level_cache.borrow().get(&id).copied() {
            return level;
        }
        let level = match self.arena.get_pos(id) {
            Pos::Bot => 0,
            Pos::Atom(atom) => self.max_level_atom(&atom),
            Pos::Var(tv) | Pos::Raw(tv) => self.level_of(tv),
            Pos::Forall(_, body) => self.max_level_pos(body),
            Pos::Con(_, args) => args
                .iter()
                .map(|(p, n)| self.max_level_pos(*p).max(self.max_level_neg(*n)))
                .max()
                .unwrap_or(0),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self
                .max_level_neg(arg)
                .max(self.max_level_neg(arg_eff))
                .max(self.max_level_pos(ret_eff))
                .max(self.max_level_pos(ret)),
            Pos::Record(fields) => fields
                .iter()
                .map(|field| self.max_level_pos(field.value))
                .max()
                .unwrap_or(0),
            Pos::RecordTailSpread { fields, tail } => fields
                .iter()
                .map(|field| self.max_level_pos(field.value))
                .max()
                .unwrap_or(0)
                .max(self.max_level_pos(tail)),
            Pos::RecordHeadSpread { tail, fields } => fields
                .iter()
                .map(|field| self.max_level_pos(field.value))
                .max()
                .unwrap_or(0)
                .max(self.max_level_pos(tail)),
            Pos::PolyVariant(items) => items
                .iter()
                .flat_map(|(_, ps)| ps)
                .map(|p| self.max_level_pos(*p))
                .max()
                .unwrap_or(0),
            Pos::Tuple(items) => items
                .iter()
                .map(|p| self.max_level_pos(*p))
                .max()
                .unwrap_or(0),
            Pos::Row(items, tail) => items
                .iter()
                .map(|p| self.max_level_pos(*p))
                .max()
                .unwrap_or(0)
                .max(self.max_level_pos(tail)),
            Pos::Union(a, b) => self.max_level_pos(a).max(self.max_level_pos(b)),
        };
        self.pos_max_level_cache.borrow_mut().insert(id, level);
        level
    }

    fn max_level_neg(&self, id: NegId) -> u32 {
        if let Some(level) = self.neg_max_level_cache.borrow().get(&id).copied() {
            return level;
        }
        let level = match self.arena.get_neg(id) {
            Neg::Top => 0,
            Neg::Atom(atom) => self.max_level_atom(&atom),
            Neg::Var(tv) => self.level_of(tv),
            Neg::Forall(_, body) => self.max_level_neg(body),
            Neg::Con(_, args) => args
                .iter()
                .map(|(p, n)| self.max_level_pos(*p).max(self.max_level_neg(*n)))
                .max()
                .unwrap_or(0),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self
                .max_level_pos(arg)
                .max(self.max_level_pos(arg_eff))
                .max(self.max_level_neg(ret_eff))
                .max(self.max_level_neg(ret)),
            Neg::Record(fields) => fields
                .iter()
                .map(|field| self.max_level_neg(field.value))
                .max()
                .unwrap_or(0),
            Neg::PolyVariant(items) => items
                .iter()
                .flat_map(|(_, ns)| ns)
                .map(|n| self.max_level_neg(*n))
                .max()
                .unwrap_or(0),
            Neg::Tuple(items) => items
                .iter()
                .map(|n| self.max_level_neg(*n))
                .max()
                .unwrap_or(0),
            Neg::Row(items, tail) => items
                .iter()
                .map(|n| self.max_level_neg(*n))
                .max()
                .unwrap_or(0)
                .max(self.max_level_neg(tail)),
            Neg::Intersection(a, b) => self.max_level_neg(a).max(self.max_level_neg(b)),
        };
        self.neg_max_level_cache.borrow_mut().insert(id, level);
        level
    }

    fn max_level_atom(&self, atom: &EffectAtom) -> u32 {
        atom.args
            .iter()
            .map(|(pos, neg)| self.level_of(*pos).max(self.level_of(*neg)))
            .max()
            .unwrap_or(0)
    }

    // === 診断: 暴走源特定（YULANG_EXTRUDE_LIMIT 設定時のみ有効）===
    fn bump_extrude_counter(&self, tv: TypeVar, target_lvl: u32) {
        let limit = std::env::var("YULANG_EXTRUDE_LIMIT")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        if limit == 0 {
            return;
        }
        let count = self.extrude_call_count.get() + 1;
        self.extrude_call_count.set(count);
        if count == limit {
            panic!(
                "extrude limit {limit} 到達。tv{} target_lvl={target_lvl} level={} lowers={} uppers={} compact={}",
                tv.0,
                self.level_of(tv),
                self.lower_refs_of(tv).len(),
                self.upper_refs_of(tv).len(),
                self.compact_lower_instances_of(tv).len(),
            );
        }
    }
}

#[derive(Debug)]
struct ExtrudeCtx {
    target_lvl: u32,
    /// 老化済みの変数。bounds のサイクルで無限再帰しないためのガード（論文の cache c）。
    visited: FxHashSet<TypeVar>,
}

impl ExtrudeCtx {
    fn new(target_lvl: u32) -> Self {
        Self {
            target_lvl,
            visited: FxHashSet::default(),
        }
    }
}
