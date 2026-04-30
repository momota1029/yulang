use super::Infer;
use crate::ids::{NegId, PosId};
use crate::types::{Neg, Pos};

impl Infer {
    /// Pos 中の型変数のレベルを target_lvl 以下に in-place で下げ、同じ PosId を返す。
    pub fn extrude_pos(&self, pos: PosId, target_lvl: u32) -> PosId {
        if self.max_level_pos(pos) > target_lvl {
            self.lower_levels_pos(pos, target_lvl);
        }
        pos
    }

    pub fn extrude_neg(&self, neg: NegId, target_lvl: u32) -> NegId {
        if self.max_level_neg(neg) > target_lvl {
            self.lower_levels_neg(neg, target_lvl);
        }
        neg
    }

    fn max_level_pos(&self, id: PosId) -> u32 {
        match self.arena.get_pos(id) {
            Pos::Bot | Pos::Atom(_) => 0,
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
        }
    }

    fn max_level_neg(&self, id: NegId) -> u32 {
        match self.arena.get_neg(id) {
            Neg::Top | Neg::Atom(_) => 0,
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
        }
    }

    fn lower_levels_pos(&self, id: PosId, target_lvl: u32) {
        match self.arena.get_pos(id) {
            Pos::Bot | Pos::Atom(_) | Pos::Forall(..) => {}
            Pos::Var(vs) | Pos::Raw(vs) => {
                if self.level_of(vs) <= target_lvl {
                    return;
                }
                self.register_level(vs, target_lvl);
                for lb in self.lower_refs_of(vs) {
                    self.lower_levels_pos(lb, target_lvl);
                }
            }
            Pos::Con(_, args) => {
                for (p, n) in args {
                    self.lower_levels_pos(p, target_lvl);
                    self.lower_levels_neg(n, target_lvl);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.lower_levels_neg(arg, target_lvl);
                self.lower_levels_neg(arg_eff, target_lvl);
                self.lower_levels_pos(ret_eff, target_lvl);
                self.lower_levels_pos(ret, target_lvl);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.lower_levels_pos(field.value, target_lvl);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.lower_levels_pos(field.value, target_lvl);
                }
                self.lower_levels_pos(tail, target_lvl);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.lower_levels_pos(tail, target_lvl);
                for field in fields {
                    self.lower_levels_pos(field.value, target_lvl);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, ps) in items {
                    for p in ps {
                        self.lower_levels_pos(p, target_lvl);
                    }
                }
            }
            Pos::Tuple(items) => {
                for p in items {
                    self.lower_levels_pos(p, target_lvl);
                }
            }
            Pos::Row(items, tail) => {
                for p in items {
                    self.lower_levels_pos(p, target_lvl);
                }
                self.lower_levels_pos(tail, target_lvl);
            }
            Pos::Union(a, b) => {
                self.lower_levels_pos(a, target_lvl);
                self.lower_levels_pos(b, target_lvl);
            }
        }
    }

    fn lower_levels_neg(&self, id: NegId, target_lvl: u32) {
        match self.arena.get_neg(id) {
            Neg::Top | Neg::Atom(_) | Neg::Forall(..) => {}
            Neg::Var(vs) => {
                if self.level_of(vs) <= target_lvl {
                    return;
                }
                self.register_level(vs, target_lvl);
                for ub in self.upper_refs_of(vs) {
                    self.lower_levels_neg(ub, target_lvl);
                }
            }
            Neg::Con(_, args) => {
                for (p, n) in args {
                    self.lower_levels_pos(p, target_lvl);
                    self.lower_levels_neg(n, target_lvl);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.lower_levels_pos(arg, target_lvl);
                self.lower_levels_pos(arg_eff, target_lvl);
                self.lower_levels_neg(ret_eff, target_lvl);
                self.lower_levels_neg(ret, target_lvl);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.lower_levels_neg(field.value, target_lvl);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, ns) in items {
                    for n in ns {
                        self.lower_levels_neg(n, target_lvl);
                    }
                }
            }
            Neg::Tuple(items) => {
                for n in items {
                    self.lower_levels_neg(n, target_lvl);
                }
            }
            Neg::Row(items, tail) => {
                for n in items {
                    self.lower_levels_neg(n, target_lvl);
                }
                self.lower_levels_neg(tail, target_lvl);
            }
            Neg::Intersection(a, b) => {
                self.lower_levels_neg(a, target_lvl);
                self.lower_levels_neg(b, target_lvl);
            }
        }
    }
}
