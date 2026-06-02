use super::Infer;
use crate::ids::{NegId, PosId, TypeVar, fresh_type_var};
use crate::types::{EffectAtom, Neg, Pos};

impl Infer {
    /// Simple-sub の extrusion。
    ///
    /// 低レベル変数の境界に高レベル変数を直接入れず、高レベル側の構造を
    /// target level の近似変数へコピーする。元の変数 level は変えない。
    pub fn extrude_pos(&self, pos: PosId, target_lvl: u32) -> PosId {
        if self.max_level_pos(pos) <= target_lvl {
            return pos;
        }
        let mut ctx = ExtrudeCtx::new(target_lvl);
        self.extrude_pos_id(pos, ExtrudePolarity::Positive, &mut ctx)
    }

    pub fn extrude_neg(&self, neg: NegId, target_lvl: u32) -> NegId {
        if self.max_level_neg(neg) <= target_lvl {
            return neg;
        }
        let mut ctx = ExtrudeCtx::new(target_lvl);
        self.extrude_neg_id(neg, ExtrudePolarity::Negative, &mut ctx)
    }

    fn extrude_pos_id(&self, id: PosId, pol: ExtrudePolarity, ctx: &mut ExtrudeCtx) -> PosId {
        if self.max_level_pos(id) <= ctx.target_lvl {
            return id;
        }
        let key = (id, ctx.target_lvl, pol);
        if let Some(cached) = self.extrude_pos_cache.borrow().get(&key).copied() {
            return cached;
        }
        let node = match self.arena.get_pos(id) {
            Pos::Bot => Pos::Bot,
            Pos::Var(tv) => Pos::Var(self.extrude_type_var(tv, pol, ctx)),
            Pos::Raw(tv) => Pos::Raw(self.extrude_type_var(tv, pol, ctx)),
            Pos::Atom(atom) => Pos::Atom(self.extrude_effect_atom(atom, pol, ctx)),
            Pos::Forall(vars, body) => Pos::Forall(vars, self.extrude_pos_id(body, pol, ctx)),
            Pos::Con(path, args) => Pos::Con(
                path,
                args.into_iter()
                    .map(|(pos, neg)| {
                        (
                            self.extrude_pos_id(pos, pol, ctx),
                            self.extrude_neg_id(neg, pol.flip(), ctx),
                        )
                    })
                    .collect(),
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.extrude_neg_id(arg, pol.flip(), ctx),
                arg_eff: self.extrude_neg_id(arg_eff, pol.flip(), ctx),
                ret_eff: self.extrude_pos_id(ret_eff, pol, ctx),
                ret: self.extrude_pos_id(ret, pol, ctx),
            },
            Pos::Record(fields) => Pos::Record(
                fields
                    .into_iter()
                    .map(|mut field| {
                        field.value = self.extrude_pos_id(field.value, pol, ctx);
                        field
                    })
                    .collect(),
            ),
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: fields
                    .into_iter()
                    .map(|mut field| {
                        field.value = self.extrude_pos_id(field.value, pol, ctx);
                        field
                    })
                    .collect(),
                tail: self.extrude_pos_id(tail, pol, ctx),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.extrude_pos_id(tail, pol, ctx),
                fields: fields
                    .into_iter()
                    .map(|mut field| {
                        field.value = self.extrude_pos_id(field.value, pol, ctx);
                        field
                    })
                    .collect(),
            },
            Pos::PolyVariant(items) => Pos::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.extrude_pos_id(payload, pol, ctx))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => Pos::Tuple(
                items
                    .into_iter()
                    .map(|item| self.extrude_pos_id(item, pol, ctx))
                    .collect(),
            ),
            Pos::Row(items, tail) => Pos::Row(
                items
                    .into_iter()
                    .map(|item| self.extrude_pos_id(item, pol, ctx))
                    .collect(),
                self.extrude_pos_id(tail, pol, ctx),
            ),
            Pos::Union(left, right) => Pos::Union(
                self.extrude_pos_id(left, pol, ctx),
                self.extrude_pos_id(right, pol, ctx),
            ),
        };
        let result = self.alloc_pos(node);
        self.extrude_pos_cache.borrow_mut().insert(key, result);
        result
    }

    fn extrude_neg_id(&self, id: NegId, pol: ExtrudePolarity, ctx: &mut ExtrudeCtx) -> NegId {
        if self.max_level_neg(id) <= ctx.target_lvl {
            return id;
        }
        let key = (id, ctx.target_lvl, pol);
        if let Some(cached) = self.extrude_neg_cache.borrow().get(&key).copied() {
            return cached;
        }
        let node = match self.arena.get_neg(id) {
            Neg::Top => Neg::Top,
            Neg::Var(tv) => Neg::Var(self.extrude_type_var(tv, pol, ctx)),
            Neg::Atom(atom) => Neg::Atom(self.extrude_effect_atom(atom, pol, ctx)),
            Neg::Forall(vars, body) => Neg::Forall(vars, self.extrude_neg_id(body, pol, ctx)),
            Neg::Con(path, args) => Neg::Con(
                path,
                args.into_iter()
                    .map(|(pos, neg)| {
                        (
                            self.extrude_pos_id(pos, pol, ctx),
                            self.extrude_neg_id(neg, pol.flip(), ctx),
                        )
                    })
                    .collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.extrude_pos_id(arg, pol.flip(), ctx),
                arg_eff: self.extrude_pos_id(arg_eff, pol.flip(), ctx),
                ret_eff: self.extrude_neg_id(ret_eff, pol, ctx),
                ret: self.extrude_neg_id(ret, pol, ctx),
            },
            Neg::Record(fields) => Neg::Record(
                fields
                    .into_iter()
                    .map(|mut field| {
                        field.value = self.extrude_neg_id(field.value, pol, ctx);
                        field
                    })
                    .collect(),
            ),
            Neg::PolyVariant(items) => Neg::PolyVariant(
                items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.extrude_neg_id(payload, pol, ctx))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => Neg::Tuple(
                items
                    .into_iter()
                    .map(|item| self.extrude_neg_id(item, pol, ctx))
                    .collect(),
            ),
            Neg::Row(items, tail) => Neg::Row(
                items
                    .into_iter()
                    .map(|item| self.extrude_neg_id(item, pol, ctx))
                    .collect(),
                self.extrude_neg_id(tail, pol, ctx),
            ),
            Neg::Intersection(left, right) => Neg::Intersection(
                self.extrude_neg_id(left, pol, ctx),
                self.extrude_neg_id(right, pol, ctx),
            ),
        };
        let result = self.alloc_neg(node);
        self.extrude_neg_cache.borrow_mut().insert(key, result);
        result
    }

    fn extrude_type_var(&self, tv: TypeVar, pol: ExtrudePolarity, ctx: &mut ExtrudeCtx) -> TypeVar {
        self.bump_extrude_counter(tv, pol, ctx.target_lvl);
        if self.level_of(tv) <= ctx.target_lvl {
            return tv;
        }
        let key = (tv, ctx.target_lvl, pol);
        if let Some(copy) = self.extrude_var_cache.borrow().get(&key).copied() {
            return copy;
        }

        let copy = fresh_type_var();
        self.register_level(copy, ctx.target_lvl);
        self.extrude_var_cache.borrow_mut().insert(key, copy);
        self.extrude_origin.borrow_mut().insert(copy, tv);
        self.copy_extruded_var_side_tables(tv, copy, pol, ctx);

        match pol {
            ExtrudePolarity::Positive => {
                self.add_upper(tv, Neg::Var(copy));
                for lower in self.lower_refs_of(tv) {
                    let lower = self.extrude_pos_id(lower, pol, ctx);
                    self.add_lower_raw(copy, lower);
                }
                for instance in self.compact_lower_instances_of(tv) {
                    let lower = self.materialize_compact_lower_instance(&instance);
                    let lower = self.extrude_pos_id(lower, pol, ctx);
                    self.add_lower_raw(copy, lower);
                }
            }
            ExtrudePolarity::Negative => {
                self.add_lower_raw(tv, Pos::Var(copy));
                for upper in self.upper_refs_of(tv) {
                    let upper = self.extrude_neg_id(upper, pol, ctx);
                    self.add_upper(copy, upper);
                }
            }
        }

        copy
    }

    fn copy_extruded_var_side_tables(
        &self,
        from: TypeVar,
        to: TypeVar,
        _pol: ExtrudePolarity,
        _ctx: &mut ExtrudeCtx,
    ) {
        if let Some(origin) = self.origin_of(from) {
            self.register_origin(to, origin);
        }
        if self.effect_is_all_subtractable(from) {
            self.record_effect_subtractability(to, crate::solve::EffectSubtractability::All);
        }
        let boundary_keep = self.effect_boundary_keeps.borrow().get(&from).cloned();
        if let Some(keep) = boundary_keep {
            self.record_effect_boundary_keep(to, keep);
        }
        self.copy_effect_subtractability(from, to);
    }

    fn extrude_effect_atom(
        &self,
        atom: EffectAtom,
        pol: ExtrudePolarity,
        ctx: &mut ExtrudeCtx,
    ) -> EffectAtom {
        EffectAtom {
            path: atom.path,
            args: atom
                .args
                .into_iter()
                .map(|(pos, neg)| {
                    (
                        self.extrude_type_var(pos, pol, ctx),
                        self.extrude_type_var(neg, pol.flip(), ctx),
                    )
                })
                .collect(),
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

    // === 診断: メモリ爆食いループの暴走源特定（YULANG_EXTRUDE_LIMIT 設定時のみ有効）===
    fn bump_extrude_counter(&self, tv: TypeVar, pol: ExtrudePolarity, target_lvl: u32) {
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
                "extrude limit {limit} 到達。暴走源 tv{} pol={pol:?} target_lvl={target_lvl}\n祖先チェーン(コピー→元):\n{}",
                tv.0,
                self.dump_extrude_ancestry(tv),
            );
        }
    }

    fn dump_extrude_ancestry(&self, tv: TypeVar) -> String {
        let mut out = String::new();
        let mut cur = tv;
        let mut seen = std::collections::HashSet::new();
        let mut depth = 0usize;
        while seen.insert(cur) && depth < 80 {
            out.push_str(&format!("  [{depth}] {}\n", self.describe_var(cur)));
            match self.extrude_origin.borrow().get(&cur).copied() {
                Some(parent) => cur = parent,
                None => break,
            }
            depth += 1;
        }
        if depth >= 80 {
            out.push_str("  ... (祖先が80を超えた=祖先方向にも循環)\n");
        }
        out
    }

    fn describe_var(&self, tv: TypeVar) -> String {
        let level = self.level_of(tv);
        let owner_def = self
            .def_tvs
            .borrow()
            .iter()
            .find(|(_, v)| **v == tv)
            .map(|(d, _)| *d);
        let (kind, label) = match self.origin_of(tv) {
            Some(o) => (format!("{:?}", o.kind), o.label.unwrap_or_default()),
            None => ("?".to_string(), String::new()),
        };
        let n_lower = self.lower_refs_of(tv).len();
        let n_upper = self.upper_refs_of(tv).len();
        let n_compact = self.compact_lower_instances_of(tv).len();
        format!(
            "tv{} level={level} kind={kind} label={label:?} owner_def={owner_def:?} lowers={n_lower} uppers={n_upper} compact={n_compact}",
            tv.0
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ExtrudePolarity {
    Positive,
    Negative,
}

impl ExtrudePolarity {
    fn flip(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

// extrude のメモ化は Infer の extrude_pos_cache/neg_cache/var_cache（グローバル・永続）が担う。
// ExtrudeCtx は対象 level だけを運ぶ。
#[derive(Debug)]
struct ExtrudeCtx {
    target_lvl: u32,
}

impl ExtrudeCtx {
    fn new(target_lvl: u32) -> Self {
        Self { target_lvl }
    }
}
