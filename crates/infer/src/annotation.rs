//! pass2 で型注釈 CST を、解決済みの小さな注釈型へ読む。
//!
//! 注釈は推論済みの型そのものではない。ここでは pass1 が作った `ModuleTable` と
//! pass2 の `module` / `site` を使い、surface の型名を builtin / 型宣言 ID に解決する。
//! 後続の制約生成は、この `AnnType` を必要な polarity に応じて `Pos` / `Neg` へ落とす。

use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, StackWeight, SubtractId, Subtractability,
    TypeVar,
};
use rowan::{NodeOrToken, SyntaxNode};
use rustc_hash::{FxHashMap, FxHashSet};
use sources::Name;
use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;

use crate::{
    Arena as InferArena, ModuleId, ModuleOrder, ModuleTable, TypeDeclId, constraints::TypeLevel,
};

type Cst = SyntaxNode<YulangLanguage>;
type CstItem = NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>;

#[derive(Debug, Clone, PartialEq, Eq)]
/// 型注釈として読んだ値。
///
/// `AnnType` は pass2 で名前解決済みの注釈値で、constraint graph の型 node ではない。
pub enum AnnType {
    Builtin(BuiltinType),
    Named(TypeDeclId),
    Var(AnnTypeVar),
    Wildcard(AnnTypeVar),
    EffectRow(AnnEffectRow),
    Effectful {
        eff: AnnEffectRow,
        ret: Box<AnnType>,
    },
    Tuple(Vec<AnnType>),
    Apply {
        callee: Box<AnnType>,
        args: Vec<AnnType>,
    },
    Function {
        param: Box<AnnType>,
        arg_eff: Option<AnnEffectRow>,
        ret_eff: Option<AnnEffectRow>,
        ret: Box<AnnType>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// effect row 注釈。
///
/// `[io; 'e]` は items に `io`、tail に `'e` を持つ。`['e]` は tail だけの row として扱う。
pub struct AnnEffectRow {
    pub items: Vec<AnnEffectAtom>,
    pub tail: Option<AnnTypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// effect row 内の atom。
///
/// `_` は effect row の wildcard として、具体型名とは別に保持する。
pub enum AnnEffectAtom {
    Type(AnnType),
    Wildcard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// annotation scope 内の型変数 identity。
pub struct AnnTypeVarId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
/// 型注釈内の型変数。
///
/// `id` は annotation scope 内だけで意味を持つ。同じ scope の同名 var は同じ `id` を共有する。
pub struct AnnTypeVar {
    pub id: AnnTypeVarId,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// type `with` body の中だけで有効な `self` 型 alias。
///
/// `self` は annotation builder ごとに、その builder の型変数 scope を使って
/// `owner 'a 'b ...` へ展開される。
pub struct AnnSelfAlias {
    pub owner: TypeDeclId,
    pub type_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 注釈 builder が構造化して返す失敗。
pub enum AnnBuildError {
    ExpectedTypeExpr { kind: SyntaxKind },
    EmptyTypeExpr,
    EmptyEffectfulType,
    MissingFunctionReturn,
    MissingEffectRow,
    InvalidEffectRowTail { ty: AnnType },
    UnresolvedTypeName { path: Vec<Name> },
    UnsupportedSyntax { kind: SyntaxKind },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 注釈を接続する対象 computation。
pub struct AnnComputationTarget {
    pub value: TypeVar,
    pub effect: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnComputationConnection {
    pub subtracts: Vec<SubtractId>,
    pub effect_stack: Option<AnnEffectStackConnection>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnEffectStackConnection {
    pub inner: TypeVar,
    pub weight: StackWeight,
    pub subtracts: Vec<SubtractId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// annotation constraint lowering の失敗。
pub enum AnnConstraintError {
    MissingTypeDecl { id: TypeDeclId },
    InvalidConstructorCallee { ty: AnnType },
    InvalidEffectAtom { ty: AnnType },
    WildcardEffectRowInTypePosition,
}

/// 解決済み `AnnType` を constraint graph へ接続する。
///
/// 同じ lowerer を使う間は、同じ `AnnTypeVarId` が同じ solver `TypeVar` を共有する。
pub struct AnnConstraintLowerer<'a> {
    infer: &'a mut InferArena,
    modules: &'a ModuleTable,
    vars: FxHashMap<AnnTypeVarId, TypeVar>,
    new_var_level: Option<TypeLevel>,
}

impl<'a> AnnConstraintLowerer<'a> {
    pub fn new(infer: &'a mut InferArena, modules: &'a ModuleTable) -> Self {
        Self {
            infer,
            modules,
            vars: FxHashMap::default(),
            new_var_level: None,
        }
    }

    pub fn with_vars(
        infer: &'a mut InferArena,
        modules: &'a ModuleTable,
        vars: FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: None,
        }
    }

    pub fn with_vars_at_level(
        infer: &'a mut InferArena,
        modules: &'a ModuleTable,
        vars: FxHashMap<AnnTypeVarId, TypeVar>,
        new_var_level: TypeLevel,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: Some(new_var_level),
        }
    }

    pub fn into_vars(self) -> FxHashMap<AnnTypeVarId, TypeVar> {
        self.vars
    }

    pub fn connect_value(
        &mut self,
        target: TypeVar,
        ann: &AnnType,
    ) -> Result<Vec<SubtractId>, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        let target_upper = self.alloc_neg(Neg::Var(target));
        let target_lower = self.alloc_pos(Pos::Var(target));
        self.infer.subtype(bounds.pos, target_upper);
        self.infer.subtype(target_lower, bounds.neg);
        Ok(bounds.output_subtracts)
    }

    pub fn connect_value_upper(
        &mut self,
        target: TypeVar,
        ann: &AnnType,
    ) -> Result<Vec<SubtractId>, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        let target_lower = self.alloc_pos(Pos::Var(target));
        self.infer.subtype(target_lower, bounds.neg);
        Ok(bounds.output_subtracts)
    }

    pub fn connect_computation(
        &mut self,
        target: AnnComputationTarget,
        ann: &AnnType,
    ) -> Result<Vec<SubtractId>, AnnConstraintError> {
        self.connect_computation_detailed(target, ann)
            .map(|connection| connection.subtracts)
    }

    pub fn connect_computation_detailed(
        &mut self,
        target: AnnComputationTarget,
        ann: &AnnType,
    ) -> Result<AnnComputationConnection, AnnConstraintError> {
        match ann {
            AnnType::Effectful { eff, ret } => {
                let mut subtracts = self.connect_value(target.value, ret)?;
                let effect_stack = self.connect_effectful_annotation_effect(target.effect, eff)?;
                subtracts.extend(effect_stack.subtracts.iter().copied());
                Ok(AnnComputationConnection {
                    subtracts,
                    effect_stack: Some(effect_stack),
                })
            }
            _ => self
                .connect_value(target.value, ann)
                .map(|subtracts| AnnComputationConnection {
                    subtracts,
                    effect_stack: None,
                }),
        }
    }

    pub fn lower_role_arg(
        &mut self,
        ann: &AnnType,
    ) -> Result<crate::roles::RoleConstraintArg, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        Ok(crate::roles::RoleConstraintArg {
            lower: bounds.pos,
            upper: bounds.neg,
        })
    }

    fn lower_value_bounds(&mut self, ann: &AnnType) -> Result<AnnValueBounds, AnnConstraintError> {
        match ann {
            AnnType::Builtin(builtin) => Ok(AnnValueBounds {
                pos: self.lower_builtin_pos(*builtin),
                neg: self.lower_builtin_neg(*builtin),
                output_subtracts: Vec::new(),
            }),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Con(path.clone(), Vec::new())),
                    neg: self.alloc_neg(Neg::Con(path, Vec::new())),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Var(var) => {
                let var = self.annotation_var(var);
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Var(var)),
                    neg: self.alloc_neg(Neg::Var(var)),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Wildcard(_) => Ok(AnnValueBounds {
                pos: self.alloc_pos(Pos::Bot),
                neg: self.alloc_neg(Neg::Top),
                output_subtracts: Vec::new(),
            }),
            AnnType::EffectRow(row) => Ok(AnnValueBounds {
                pos: self.lower_effect_row_pos(row)?,
                neg: self.lower_effect_row_neg(row)?,
                output_subtracts: Vec::new(),
            }),
            AnnType::Effectful { ret, .. } => self.lower_value_bounds(ret),
            AnnType::Tuple(items) => {
                let mut pos_items = Vec::with_capacity(items.len());
                let mut neg_items = Vec::with_capacity(items.len());
                let mut output_subtracts = Vec::new();
                for item in items {
                    let bounds = self.lower_value_bounds(item)?;
                    pos_items.push(bounds.pos);
                    neg_items.push(bounds.neg);
                    output_subtracts.extend(bounds.output_subtracts);
                }
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Tuple(pos_items)),
                    neg: self.alloc_neg(Neg::Tuple(neg_items)),
                    output_subtracts,
                })
            }
            AnnType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args_from_ann(args) {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Con(path.clone(), neu_args.clone())),
                    neg: self.alloc_neg(Neg::Con(path, neu_args)),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let param = self.lower_value_bounds(param)?;
                let arg_eff = self.lower_arg_effect_bounds(arg_eff.as_ref())?;
                let ret = self.lower_value_bounds(ret)?;
                let ret_eff = self.lower_ret_effect_bounds(ret_eff.as_ref())?;
                let ret_pos = self.wrap_non_subtracts(ret.pos, &ret_eff.subtracts);
                let pos = self.alloc_pos(Pos::Fun {
                    arg: param.neg,
                    arg_eff: arg_eff.neg,
                    ret_eff: ret_eff.pos,
                    ret: ret_pos,
                });
                let neg = self.alloc_neg(Neg::Fun {
                    arg: param.pos,
                    arg_eff: arg_eff.pos,
                    ret_eff: ret_eff.neg,
                    ret: ret.neg,
                });
                Ok(AnnValueBounds {
                    pos,
                    neg,
                    output_subtracts: ret_eff.subtracts,
                })
            }
        }
    }

    fn lower_arg_effect_bounds(
        &mut self,
        row: Option<&AnnEffectRow>,
    ) -> Result<AnnEffectBounds, AnnConstraintError> {
        let Some(row) = row else {
            return Ok(self.pure_effect_bounds());
        };
        let effect = self.infer.fresh_type_var();
        self.connect_effect_row_lower(effect, row)?;
        Ok(AnnEffectBounds {
            pos: self.alloc_pos(Pos::Var(effect)),
            neg: self.alloc_neg(Neg::Var(effect)),
            subtracts: Vec::new(),
        })
    }

    fn lower_ret_effect_bounds(
        &mut self,
        row: Option<&AnnEffectRow>,
    ) -> Result<AnnEffectBounds, AnnConstraintError> {
        let Some(row) = row else {
            return Ok(self.pure_effect_bounds());
        };
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let effect = self.annotation_var(tail);
            return Ok(AnnEffectBounds {
                pos: self.alloc_pos(Pos::Var(effect)),
                neg: self.alloc_neg(Neg::Var(effect)),
                subtracts: Vec::new(),
            });
        }

        let effect = self.infer.fresh_type_var();
        self.connect_effect_tail_lower(effect, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect_pos = self.alloc_pos(Pos::Var(effect));
        let pos = self.wrap_pos_with_stack(effect_pos, &stack.weight);
        Ok(AnnEffectBounds {
            pos,
            neg: self.alloc_neg(Neg::Var(effect)),
            subtracts: stack.ids,
        })
    }

    fn pure_effect_bounds(&mut self) -> AnnEffectBounds {
        let top = self.alloc_neg(Neg::Top);
        AnnEffectBounds {
            pos: self.alloc_pos(Pos::Bot),
            neg: self.alloc_neg(Neg::Row(Vec::new(), top)),
            subtracts: Vec::new(),
        }
    }

    fn connect_effectful_annotation_effect(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<AnnEffectStackConnection, AnnConstraintError> {
        // 注釈残差は fresh な内側変数に立て、stack で包んで下から effect を抑える。
        // `stack(effect, push) <: effect` の自己辺は bounds replay で重みが際限なく
        // 合成される（spec の「自分へ戻るだけの制約は無限ループの燃料」）ため作らない。
        let inner = self.infer.fresh_type_var();
        self.connect_effect_tail_lower(inner, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(inner, &stack.weight);
        let inner_pos = self.alloc_pos(Pos::Var(inner));
        let stacked = self.wrap_pos_with_stack(inner_pos, &stack.weight);
        let upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(stacked, upper);
        Ok(AnnEffectStackConnection {
            inner,
            weight: stack.weight,
            subtracts: stack.ids,
        })
    }

    fn register_stack_facts(&mut self, var: TypeVar, weight: &StackWeight) {
        for entry in weight.entries() {
            for subtractability in &entry.stack {
                self.infer
                    .declared_subtract_fact(var, entry.id, subtractability.clone());
            }
        }
    }

    fn connect_effect_row_lower(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<(), AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Ok(());
        }
        let lower = self.lower_effect_row_pos(row)?;
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(lower, effect_upper);
        Ok(())
    }

    fn connect_effect_tail_lower(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<(), AnnConstraintError> {
        if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            let tail = self.alloc_pos(Pos::Var(tail));
            let effect = self.alloc_neg(Neg::Var(effect));
            self.infer.subtype(tail, effect);
        }
        Ok(())
    }

    fn effect_row_stack(&mut self, row: &AnnEffectRow) -> Result<EffectStack, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            let id = self.infer.fresh_subtract_id();
            return Ok(EffectStack {
                weight: StackWeight::push(id, Subtractability::All),
                ids: vec![id],
            });
        }

        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            if row.tail.is_none() {
                let id = self.infer.fresh_subtract_id();
                return Ok(EffectStack {
                    weight: StackWeight::push(id, Subtractability::Empty),
                    ids: vec![id],
                });
            }
            return Ok(EffectStack::empty());
        }

        let id = self.infer.fresh_subtract_id();
        let subtractability = subtractability_from_atoms(atoms);
        Ok(EffectStack {
            weight: StackWeight::push(id, subtractability),
            ids: vec![id],
        })
    }

    fn lower_effect_row_pos(&mut self, row: &AnnEffectRow) -> Result<PosId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let mut items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_pos(atom))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    fn lower_effect_row_neg(&mut self, row: &AnnEffectRow) -> Result<NegId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            self.alloc_neg(Neg::Var(tail))
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    fn lower_subtractable_effect_row_neg(
        &mut self,
        row: &AnnEffectRow,
    ) -> Result<NegId, AnnConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.annotation_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let effect = self.infer.fresh_type_var();
        self.connect_effect_tail_lower(effect, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect = self.alloc_neg(Neg::Var(effect));
        Ok(self.wrap_neg_with_stack(effect, &stack.weight))
    }

    fn lower_effect_atom_pos(&mut self, atom: &AnnEffectAtom) -> Result<PosId, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(ty) => self.lower_value_bounds(ty).map(|bounds| bounds.pos),
            AnnEffectAtom::Wildcard => Err(AnnConstraintError::WildcardEffectRowInTypePosition),
        }
    }

    fn lower_effect_atom_neg(&mut self, atom: &AnnEffectAtom) -> Result<NegId, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(ty) => self.lower_value_bounds(ty).map(|bounds| bounds.neg),
            AnnEffectAtom::Wildcard => Err(AnnConstraintError::WildcardEffectRowInTypePosition),
        }
    }

    fn effect_atom_con(
        &mut self,
        atom: &AnnEffectAtom,
    ) -> Result<Option<(Vec<String>, Vec<NeuId>)>, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(AnnType::Var(_)) => Ok(None),
            AnnEffectAtom::Type(ty) => self.constructor_path(ty).map(Some),
            AnnEffectAtom::Wildcard => Ok(None),
        }
    }

    fn lower_invariant_arg(&mut self, ann: &AnnType) -> Result<NeuId, AnnConstraintError> {
        let bounds = self.lower_invariant_arg_bounds(ann)?;
        Ok(self.alloc_neu(Neu::Bounds(bounds.pos, bounds.neg)))
    }

    fn lower_invariant_arg_bounds(
        &mut self,
        ann: &AnnType,
    ) -> Result<AnnValueBounds, AnnConstraintError> {
        match ann {
            AnnType::EffectRow(row) => Ok(AnnValueBounds {
                pos: self.lower_effect_row_tail_pos(row)?,
                neg: self.lower_subtractable_effect_row_neg(row)?,
                output_subtracts: Vec::new(),
            }),
            _ => self.lower_value_bounds(ann),
        }
    }

    fn lower_effect_row_tail_pos(
        &mut self,
        row: &AnnEffectRow,
    ) -> Result<PosId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let mut items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_pos(atom))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.union_pos(items))
    }

    fn lower_builtin_pos(&mut self, builtin: BuiltinType) -> PosId {
        match builtin {
            BuiltinType::Never => self.alloc_pos(Pos::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_pos(Pos::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn lower_builtin_neg(&mut self, builtin: BuiltinType) -> NegId {
        match builtin {
            BuiltinType::Never => self.alloc_neg(Neg::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_neg(Neg::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn constructor_path(
        &mut self,
        ann: &AnnType,
    ) -> Result<(Vec<String>, Vec<NeuId>), AnnConstraintError> {
        match ann {
            AnnType::Builtin(builtin) => Ok((vec![builtin.surface_name().to_string()], Vec::new())),
            AnnType::Named(id) => Ok((self.type_decl_path(*id)?, Vec::new())),
            AnnType::Apply { callee, args } => {
                let (path, mut head_args) = self.constructor_path(callee)?;
                for arg in args_from_ann(args) {
                    head_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok((path, head_args))
            }
            ty => Err(AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() }),
        }
    }

    fn type_decl_path(&self, id: TypeDeclId) -> Result<Vec<String>, AnnConstraintError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(AnnConstraintError::MissingTypeDecl { id })?;
        Ok(self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect())
    }

    fn annotation_var(&mut self, var: &AnnTypeVar) -> TypeVar {
        if let Some(found) = self.vars.get(&var.id) {
            return *found;
        }
        let ty = if let Some(level) = self.new_var_level {
            self.infer.fresh_type_var_at(level)
        } else {
            self.infer.fresh_type_var()
        };
        self.vars.insert(var.id, ty);
        ty
    }

    fn wrap_non_subtracts(&mut self, pos: PosId, subtracts: &[SubtractId]) -> PosId {
        let weight = subtracts
            .iter()
            .fold(StackWeight::empty(), |weight, subtract| {
                weight.compose(&StackWeight::pop(*subtract))
            });
        self.wrap_pos_with_stack(pos, &weight)
    }

    fn wrap_pos_with_stack(&mut self, pos: PosId, weight: &StackWeight) -> PosId {
        if weight.is_empty() {
            return pos;
        }
        self.alloc_pos(Pos::Stack {
            inner: pos,
            weight: weight.clone(),
        })
    }

    fn wrap_neg_with_stack(&mut self, neg: NegId, weight: &StackWeight) -> NegId {
        if weight.is_empty() {
            return neg;
        }
        self.alloc_neg(Neg::Stack {
            inner: neg,
            weight: weight.clone(),
        })
    }

    fn union_pos(&mut self, input: Vec<PosId>) -> PosId {
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.infer.constraints().types().pos(part), Pos::Bot)
                || parts.contains(&part)
            {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_pos(Pos::Bot);
        };
        parts
            .into_iter()
            .skip(1)
            .fold(first, |acc, part| self.alloc_pos(Pos::Union(acc, part)))
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.infer.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.infer.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.infer.alloc_neu(neu)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnValueBounds {
    pos: PosId,
    neg: NegId,
    output_subtracts: Vec<SubtractId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnEffectBounds {
    pos: PosId,
    neg: NegId,
    subtracts: Vec<SubtractId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EffectStack {
    weight: StackWeight,
    ids: Vec<SubtractId>,
}

impl EffectStack {
    fn empty() -> Self {
        Self {
            weight: StackWeight::empty(),
            ids: Vec::new(),
        }
    }
}

fn subtractability_from_atoms(atoms: Vec<(Vec<String>, Vec<NeuId>)>) -> Subtractability {
    match atoms.as_slice() {
        [] => Subtractability::Empty,
        [(path, args)] => Subtractability::Set(path.clone(), args.clone()),
        _ => Subtractability::SetMany(atoms),
    }
}

/// `TypeExpr` CST を、pass2 の scope で解決済み `AnnType` へ読む。
pub fn build_ann_type_expr(
    modules: &ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    type_expr: &Cst,
) -> Result<AnnType, AnnBuildError> {
    AnnTypeBuilder::new(modules, module, site).build_type_expr(type_expr)
}

/// pass2 の annotation scope。
///
/// 1つの関数注釈で複数の `TypeExpr` を読む必要がある場合は、同じ builder を使い回す。
/// そうすると同名の surface type variable が同じ `AnnTypeVarId` を共有する。
pub struct AnnTypeBuilder<'a> {
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
    bare_type_vars: FxHashSet<String>,
    bare_type_var_aliases: FxHashMap<String, String>,
    type_vars: FxHashMap<String, AnnTypeVarId>,
    next_type_var: u32,
}

impl<'a> AnnTypeBuilder<'a> {
    pub fn new(modules: &'a ModuleTable, module: ModuleId, site: ModuleOrder) -> Self {
        Self {
            modules,
            module,
            site,
            self_alias: None,
            bare_type_vars: FxHashSet::default(),
            bare_type_var_aliases: FxHashMap::default(),
            type_vars: FxHashMap::default(),
            next_type_var: 0,
        }
    }

    pub fn with_self_alias(
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: AnnSelfAlias,
    ) -> Self {
        let mut builder = Self::new(modules, module, site);
        builder.self_alias = Some(self_alias);
        builder
    }

    pub fn set_self_alias(&mut self, self_alias: AnnSelfAlias) {
        self.self_alias = Some(self_alias);
    }

    pub fn add_bare_type_var(&mut self, name: impl Into<String>) {
        self.bare_type_vars.insert(name.into());
    }

    pub fn add_bare_type_var_alias(&mut self, alias: impl Into<String>, target: impl Into<String>) {
        self.bare_type_var_aliases
            .insert(alias.into(), target.into());
    }

    pub fn ann_type_var_for_role(&mut self, name: &str) -> AnnTypeVar {
        self.ann_type_var(name)
    }

    pub fn type_var_bindings(&self) -> Vec<(String, AnnTypeVarId)> {
        self.type_vars
            .iter()
            .map(|(name, id)| (name.clone(), *id))
            .collect()
    }

    pub fn seed_type_var_bindings(&mut self, bindings: &[(String, AnnTypeVarId)]) {
        for (name, id) in bindings {
            self.type_vars.insert(name.clone(), *id);
            self.next_type_var = self.next_type_var.max(id.0.saturating_add(1));
        }
    }

    pub fn self_alias_type(&mut self) -> Option<AnnType> {
        let alias = self.self_alias.clone()?;
        Some(self.type_decl_application(alias.owner, &alias.type_vars))
    }

    pub fn type_decl_application(&mut self, owner: TypeDeclId, type_vars: &[String]) -> AnnType {
        let args = type_vars
            .iter()
            .map(|name| AnnType::Var(self.ann_type_var(name)))
            .collect::<Vec<_>>();
        if args.is_empty() {
            AnnType::Named(owner)
        } else {
            AnnType::Apply {
                callee: Box::new(AnnType::Named(owner)),
                args,
            }
        }
    }

    /// `TypeExpr` CST を、pass2 の scope で解決済み `AnnType` へ読む。
    pub fn build_type_expr(&mut self, type_expr: &Cst) -> Result<AnnType, AnnBuildError> {
        if type_expr.kind() != SyntaxKind::TypeExpr {
            return Err(AnnBuildError::ExpectedTypeExpr {
                kind: type_expr.kind(),
            });
        }
        if let Some(arrow) = type_expr
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeArrow)
        {
            let param = self.build_type_head(type_expr)?;
            let arg_eff = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeRow)
                .map(|row| self.build_effect_row(&row))
                .transpose()?;
            let ret = arrow
                .children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
                .ok_or(AnnBuildError::MissingFunctionReturn)?;
            let (ret_eff, ret) = split_effectful_return(self.build_type_expr(&ret)?);
            return Ok(AnnType::Function {
                param: Box::new(param),
                arg_eff,
                ret_eff,
                ret: Box::new(ret),
            });
        }

        self.build_type_head(type_expr)
    }

    fn build_type_head(&mut self, type_expr: &Cst) -> Result<AnnType, AnnBuildError> {
        let items = type_expr
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
            .filter(|item| {
                !matches!(item, NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeArrow)
            })
            .collect::<Vec<_>>();

        let Some(first) = items.first() else {
            return Err(AnnBuildError::EmptyTypeExpr);
        };

        if let NodeOrToken::Node(row) = first
            && row.kind() == SyntaxKind::TypeRow
        {
            let ret_items = &items[1..];
            let Some(ret_first) = ret_items.first() else {
                return Err(AnnBuildError::EmptyEffectfulType);
            };
            let (ret, next) = self.build_type_base(ret_items, ret_first)?;
            return Ok(AnnType::Effectful {
                eff: self.build_effect_row(row)?,
                ret: Box::new(self.build_type_applications(ret, &ret_items[next..])?),
            });
        }

        let (base, next) = self.build_type_base(&items, first)?;
        self.build_type_applications(base, &items[next..])
    }

    fn build_type_base(
        &mut self,
        items: &[CstItem],
        first: &CstItem,
    ) -> Result<(AnnType, usize), AnnBuildError> {
        match first {
            NodeOrToken::Token(token)
                if token.kind() == SyntaxKind::Ident && token.text() == "_" =>
            {
                Ok((AnnType::Wildcard(self.ann_wildcard_type()), 1))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                let (path, next) = parse_ann_path_prefix(items)?;
                Ok((self.resolve_ann_path(path)?, next))
            }
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::SigilIdent => {
                Ok((AnnType::Var(self.ann_type_var(token.text())), 1))
            }
            NodeOrToken::Token(token) => {
                Err(AnnBuildError::UnsupportedSyntax { kind: token.kind() })
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeParenGroup => {
                Ok((self.build_type_paren_group(node)?, 1))
            }
            NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeEffectRow => {
                Ok((AnnType::EffectRow(self.build_type_effect_row(node)?), 1))
            }
            NodeOrToken::Node(node) => Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn build_type_applications(
        &mut self,
        base: AnnType,
        suffixes: &[CstItem],
    ) -> Result<AnnType, AnnBuildError> {
        let mut args = Vec::new();
        for item in suffixes {
            let NodeOrToken::Node(node) = item else {
                let kind = item
                    .as_token()
                    .map(|token| token.kind())
                    .unwrap_or(SyntaxKind::TypeExpr);
                return Err(AnnBuildError::UnsupportedSyntax { kind });
            };
            match node.kind() {
                SyntaxKind::TypeApply => {
                    args.push(self.build_single_type_arg(node)?);
                }
                SyntaxKind::TypeCall => {
                    let call_args = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
                        .map(|child| self.build_type_expr(&child))
                        .collect::<Result<Vec<_>, _>>()?;
                    if call_args.is_empty() {
                        return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() });
                    }
                    args.extend(call_args);
                }
                _ => return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() }),
            }
        }

        if args.is_empty() {
            Ok(base)
        } else {
            Ok(AnnType::Apply {
                callee: Box::new(base),
                args,
            })
        }
    }

    fn build_single_type_arg(&mut self, apply: &Cst) -> Result<AnnType, AnnBuildError> {
        let children = apply
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        let [child] = children.as_slice() else {
            return Err(AnnBuildError::UnsupportedSyntax { kind: apply.kind() });
        };
        self.build_type_expr(child)
    }

    fn build_type_paren_group(&mut self, group: &Cst) -> Result<AnnType, AnnBuildError> {
        let children = group
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpr)
            .collect::<Vec<_>>();
        match children.as_slice() {
            [] => Ok(AnnType::Builtin(BuiltinType::Unit)),
            [child] => self.build_type_expr(child),
            _ => children
                .iter()
                .map(|child| self.build_type_expr(child))
                .collect::<Result<Vec<_>, _>>()
                .map(AnnType::Tuple),
        }
    }

    fn build_type_effect_row(&mut self, effect_row: &Cst) -> Result<AnnEffectRow, AnnBuildError> {
        let row = effect_row
            .children()
            .find(|child| child.kind() == SyntaxKind::TypeRow)
            .ok_or(AnnBuildError::MissingEffectRow)?;
        self.build_effect_row(&row)
    }

    fn build_effect_row(&mut self, row: &Cst) -> Result<AnnEffectRow, AnnBuildError> {
        let mut items = Vec::new();
        let mut tail = None;
        let mut seen_tail_separator = false;

        for item in row
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item))
        {
            match item {
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeExpr => {
                    if !seen_tail_separator && is_wildcard_type_expr(&node) {
                        items.push(AnnEffectAtom::Wildcard);
                        continue;
                    }
                    let ty = self.build_type_expr(&node)?;
                    if seen_tail_separator {
                        let AnnType::Var(var) = ty else {
                            return Err(AnnBuildError::InvalidEffectRowTail { ty });
                        };
                        tail = Some(var);
                    } else {
                        items.push(AnnEffectAtom::Type(ty));
                    }
                }
                NodeOrToken::Node(node)
                    if node.kind() == SyntaxKind::Separator && separator_has_semicolon(&node) =>
                {
                    seen_tail_separator = true;
                }
                NodeOrToken::Node(node) if node.kind() == SyntaxKind::Separator => {}
                NodeOrToken::Node(node) => {
                    return Err(AnnBuildError::UnsupportedSyntax { kind: node.kind() });
                }
                NodeOrToken::Token(token) => match token.kind() {
                    SyntaxKind::BracketL | SyntaxKind::BracketR | SyntaxKind::Comma => {}
                    SyntaxKind::Semicolon => seen_tail_separator = true,
                    kind => return Err(AnnBuildError::UnsupportedSyntax { kind }),
                },
            }
        }

        if !seen_tail_separator
            && tail.is_none()
            && items.len() == 1
            && let AnnEffectAtom::Type(AnnType::Var(var)) = &items[0]
        {
            return Ok(AnnEffectRow {
                items: Vec::new(),
                tail: Some(var.clone()),
            });
        }

        Ok(AnnEffectRow { items, tail })
    }

    fn resolve_ann_path(&mut self, path: Vec<Name>) -> Result<AnnType, AnnBuildError> {
        if let [name] = path.as_slice() {
            if name.0 == "self"
                && let Some(ty) = self.self_alias_type()
            {
                return Ok(ty);
            }
            if let Some(builtin) = BuiltinType::from_surface_name(name.0.as_str()) {
                return Ok(AnnType::Builtin(builtin));
            }
            if let Some(target) = self.bare_type_var_aliases.get(&name.0).cloned() {
                return Ok(AnnType::Var(self.ann_type_var(&target)));
            }
            if self.bare_type_vars.contains(&name.0) {
                return Ok(AnnType::Var(self.ann_type_var(&name.0)));
            }
            if let Some(decl) = self.modules.lexical_type_at(self.module, name, self.site) {
                return Ok(AnnType::Named(decl.id));
            }
            return Err(AnnBuildError::UnresolvedTypeName { path });
        }

        let Some((last, prefix)) = path.split_last() else {
            return Err(AnnBuildError::EmptyTypeExpr);
        };
        let Some(module) = self.resolve_module_prefix(prefix) else {
            return Err(AnnBuildError::UnresolvedTypeName { path });
        };
        let Some(decl) = self.modules.type_at(module, last, module_path_site()) else {
            return Err(AnnBuildError::UnresolvedTypeName { path });
        };
        Ok(AnnType::Named(decl.id))
    }

    fn resolve_module_prefix(&self, path: &[Name]) -> Option<ModuleId> {
        let (first, rest) = path.split_first()?;
        let mut current = self
            .modules
            .lexical_module_at(self.module, first, self.site)?;
        for segment in rest {
            current = self
                .modules
                .module_at(current, segment, module_path_site())?;
        }
        Some(current)
    }

    fn ann_type_var(&mut self, text: &str) -> AnnTypeVar {
        let name = ann_type_var_name(text);
        let id = if let Some(id) = self.type_vars.get(&name) {
            *id
        } else {
            let id = AnnTypeVarId(self.next_type_var);
            self.next_type_var += 1;
            self.type_vars.insert(name.clone(), id);
            id
        };
        AnnTypeVar { id, name }
    }

    fn ann_wildcard_type(&mut self) -> AnnTypeVar {
        let id = AnnTypeVarId(self.next_type_var);
        self.next_type_var += 1;
        AnnTypeVar {
            id,
            name: format!("_{}", id.0),
        }
    }
}

fn split_effectful_return(ret: AnnType) -> (Option<AnnEffectRow>, AnnType) {
    match ret {
        AnnType::Effectful { eff, ret } => (Some(eff), *ret),
        ret => (None, ret),
    }
}

fn parse_ann_path_prefix(items: &[CstItem]) -> Result<(Vec<Name>, usize), AnnBuildError> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return Err(AnnBuildError::EmptyTypeExpr);
    };
    if head.kind() != SyntaxKind::Ident {
        return Err(AnnBuildError::UnsupportedSyntax { kind: head.kind() });
    }

    let mut segments = vec![Name(head.text().to_string())];
    let mut next = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }

        let Some(segment) = path_sep
            .children_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
        else {
            return Err(AnnBuildError::UnsupportedSyntax {
                kind: path_sep.kind(),
            });
        };
        segments.push(Name(segment.text().to_string()));
        next += 1;
    }

    Ok((segments, next))
}

fn ann_type_var_name(text: &str) -> String {
    text.trim_start_matches('\'').to_string()
}

fn args_from_ann(args: &[AnnType]) -> impl Iterator<Item = &AnnType> {
    args.iter()
}

fn effect_row_has_wildcard(row: &AnnEffectRow) -> bool {
    row.items
        .iter()
        .any(|atom| matches!(atom, AnnEffectAtom::Wildcard))
}

fn is_wildcard_type_expr(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Ident && token.text() == "_")
}

fn separator_has_semicolon(node: &Cst) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Semicolon)
}

fn module_path_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

fn item_is_trivia(item: &CstItem) -> bool {
    item.as_token().is_some_and(|token| {
        matches!(
            token.kind(),
            SyntaxKind::Space | SyntaxKind::LineComment | SyntaxKind::BlockComment
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_annotation(src: &str) -> AnnType {
        let root = parse(src);
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let type_expr = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation");
        build_ann_type_expr(&lower.modules, module, site, &type_expr)
            .expect("annotation should build")
    }

    fn build_annotation_error(src: &str) -> AnnBuildError {
        let root = parse(src);
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let type_expr = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation");
        build_ann_type_expr(&lower.modules, module, site, &type_expr)
            .expect_err("annotation should fail")
    }

    #[test]
    fn builds_builtin_annotations() {
        assert_eq!(
            build_annotation("my site: int = 1\n"),
            AnnType::Builtin(BuiltinType::Int)
        );
        assert_eq!(
            build_annotation("my site: float = 1\n"),
            AnnType::Builtin(BuiltinType::Float)
        );
        assert_eq!(
            build_annotation("my site: unit = 1\n"),
            AnnType::Builtin(BuiltinType::Unit)
        );
    }

    #[test]
    fn builds_unit_paren_annotation_as_builtin_unit() {
        assert_eq!(
            build_annotation("my site: () = 1\n"),
            AnnType::Builtin(BuiltinType::Unit)
        );
    }

    #[test]
    fn builds_local_named_annotation() {
        let root = parse("type User\nmy site: User = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].id;
        let type_expr = first_type_expr(&root);

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &type_expr),
            Ok(AnnType::Named(user))
        );
    }

    #[test]
    fn builds_imported_alias_and_glob_annotations() {
        let alias_root = parse("mod m:\n  type User\nuse m::User as Alias\nmy site: Alias = 1\n");
        let alias_lower = crate::lower_module_map(&alias_root);
        let alias_module = alias_lower.modules.root_id();
        let alias_site = alias_lower
            .modules
            .value_decls(alias_module, &Name("site".into()))[0]
            .order;
        let m = alias_lower
            .modules
            .module_decls(alias_module, &Name("m".into()))[0]
            .module;
        let user = alias_lower.modules.type_decls(m, &Name("User".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &alias_lower.modules,
                alias_module,
                alias_site,
                &first_type_expr(&alias_root)
            ),
            Ok(AnnType::Named(user))
        );

        let glob_root = parse("mod m:\n  type User\nuse m::*\nmy site: User = 1\n");
        let glob_lower = crate::lower_module_map(&glob_root);
        let glob_module = glob_lower.modules.root_id();
        let glob_site = glob_lower
            .modules
            .value_decls(glob_module, &Name("site".into()))[0]
            .order;
        let m = glob_lower
            .modules
            .module_decls(glob_module, &Name("m".into()))[0]
            .module;
        let user = glob_lower.modules.type_decls(m, &Name("User".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &glob_lower.modules,
                glob_module,
                glob_site,
                &first_type_expr(&glob_root)
            ),
            Ok(AnnType::Named(user))
        );
    }

    #[test]
    fn builds_qualified_path_annotation() {
        let root = parse("mod std:\n  mod num:\n    type Int\nmy site: std::num::Int = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
        let num = lower.modules.module_decls(std, &Name("num".into()))[0].module;
        let int = lower.modules.type_decls(num, &Name("Int".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(AnnType::Named(int))
        );
    }

    #[test]
    fn builds_right_associative_function_annotations() {
        assert_eq!(
            build_annotation("my site: int -> float -> unit = 1\n"),
            AnnType::Function {
                param: Box::new(AnnType::Builtin(BuiltinType::Int)),
                arg_eff: None,
                ret_eff: None,
                ret: Box::new(AnnType::Function {
                    param: Box::new(AnnType::Builtin(BuiltinType::Float)),
                    arg_eff: None,
                    ret_eff: None,
                    ret: Box::new(AnnType::Builtin(BuiltinType::Unit)),
                }),
            }
        );
    }

    #[test]
    fn builds_effect_row_annotations() {
        let root = parse("type io\ntype Foo\nmy site: Foo '['e] = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let foo = lower.modules.type_decls(module, &Name("Foo".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(ann_apply(
                AnnType::Named(foo),
                vec![AnnType::EffectRow(ann_row(Vec::new(), Some(("e", 0))))]
            ))
        );

        let row_root = parse("type io\nmy site: '[io] = 1\n");
        let row_lower = crate::lower_module_map(&row_root);
        let row_module = row_lower.modules.root_id();
        let row_site = row_lower
            .modules
            .value_decls(row_module, &Name("site".into()))[0]
            .order;
        let io = row_lower.modules.type_decls(row_module, &Name("io".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &row_lower.modules,
                row_module,
                row_site,
                &first_type_expr(&row_root)
            ),
            Ok(AnnType::EffectRow(ann_row(vec![AnnType::Named(io)], None)))
        );
    }

    #[test]
    fn builds_wildcard_effect_row_atom() {
        assert_eq!(
            build_annotation("my site: [_] int = 1\n"),
            AnnType::Effectful {
                eff: AnnEffectRow {
                    items: vec![AnnEffectAtom::Wildcard],
                    tail: None,
                },
                ret: Box::new(AnnType::Builtin(BuiltinType::Int)),
            }
        );
    }

    #[test]
    fn shares_type_vars_by_name_in_function_annotation() {
        let root = parse("type io\nmy site: 'a [io; 'e] -> ['e] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let io = lower.modules.type_decls(module, &Name("io".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(AnnType::Function {
                param: Box::new(ann_var_id("a", 0)),
                arg_eff: Some(ann_row(vec![AnnType::Named(io)], Some(("e", 1)))),
                ret_eff: Some(ann_row(Vec::new(), Some(("e", 1)))),
                ret: Box::new(ann_var_id("a", 0)),
            })
        );
    }

    #[test]
    fn shared_builder_reuses_type_vars_across_type_exprs() {
        let root = parse("my left: 'a = 1\nmy right: 'a = 2\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("right".into()))[0].order;
        let mut builder = AnnTypeBuilder::new(&lower.modules, module, site);
        let mut type_exprs = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeExpr);
        let left = type_exprs.next().expect("left annotation should exist");
        let right = type_exprs.next().expect("right annotation should exist");

        assert_eq!(builder.build_type_expr(&left), Ok(ann_var_id("a", 0)));
        assert_eq!(builder.build_type_expr(&right), Ok(ann_var_id("a", 0)));
    }

    #[test]
    fn self_alias_expands_in_builder_type_var_scope() {
        let root = parse("type box 'a\nmy site: self = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let owner = lower.modules.type_decls(module, &Name("box".into()))[0].id;
        let mut builder = AnnTypeBuilder::with_self_alias(
            &lower.modules,
            module,
            site,
            AnnSelfAlias {
                owner,
                type_vars: vec!["a".into()],
            },
        );

        assert_eq!(
            builder.build_type_expr(&first_type_expr(&root)),
            Ok(ann_apply(AnnType::Named(owner), vec![ann_var_id("a", 0)]))
        );
    }

    #[test]
    fn reports_unresolved_type_name() {
        assert_eq!(
            build_annotation_error("my site: Missing = 1\n"),
            AnnBuildError::UnresolvedTypeName {
                path: vec![Name("Missing".into())]
            }
        );
    }

    #[test]
    fn builds_type_application_annotations() {
        let root = parse(
            "type list\ntype dict\ntype string\nmod std:\n  mod num:\n    type Int\nmy site: dict(string, std::num::Int) = 1\n",
        );
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let dict = lower.modules.type_decls(module, &Name("dict".into()))[0].id;
        let string = lower.modules.type_decls(module, &Name("string".into()))[0].id;
        let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
        let num = lower.modules.module_decls(std, &Name("num".into()))[0].module;
        let int = lower.modules.type_decls(num, &Name("Int".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(ann_apply(
                AnnType::Named(dict),
                vec![AnnType::Named(string), AnnType::Named(int)]
            ))
        );

        let list_root = parse("type list\nmy site: list int = 1\n");
        let list_lower = crate::lower_module_map(&list_root);
        let list_module = list_lower.modules.root_id();
        let list_site = list_lower
            .modules
            .value_decls(list_module, &Name("site".into()))[0]
            .order;
        let list = list_lower
            .modules
            .type_decls(list_module, &Name("list".into()))[0]
            .id;

        assert_eq!(
            build_ann_type_expr(
                &list_lower.modules,
                list_module,
                list_site,
                &first_type_expr(&list_root)
            ),
            Ok(ann_apply(
                AnnType::Named(list),
                vec![AnnType::Builtin(BuiltinType::Int)]
            ))
        );

        let result_root = parse("type result\nmy site: result 't = 1\n");
        let result_lower = crate::lower_module_map(&result_root);
        let result_module = result_lower.modules.root_id();
        let result_site = result_lower
            .modules
            .value_decls(result_module, &Name("site".into()))[0]
            .order;
        let result = result_lower
            .modules
            .type_decls(result_module, &Name("result".into()))[0]
            .id;

        assert_eq!(
            build_ann_type_expr(
                &result_lower.modules,
                result_module,
                result_site,
                &first_type_expr(&result_root)
            ),
            Ok(ann_apply(AnnType::Named(result), vec![ann_var_id("t", 0)]))
        );
    }

    #[test]
    fn effect_row_type_argument_lowers_as_effect_tail() {
        let root = parse("type io\ntype Box\nmy site: Box '[io] = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let io = lower.modules.type_decls(module, &Name("io".into()))[0].id;
        let expected = type_decl_path(&lower.modules, io);
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();

        let bounds = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .lower_value_bounds(&ann)
            .expect("annotation constraints should lower");

        let types = infer.constraints().types();
        let Pos::Con(_, args) = types.pos(bounds.pos) else {
            panic!("expected constructor lower bound");
        };
        let [arg] = args.as_slice() else {
            panic!("expected one type argument");
        };
        let Neu::Bounds(lower, upper) = types.neu(*arg) else {
            panic!("expected invariant type argument bounds");
        };
        assert!(
            matches!(types.pos(*lower), Pos::Con(path, args) if path == &expected && args.is_empty()),
            "effect row argument lower should expose the row item as the effect tail type, got {:?}",
            types.pos(*lower)
        );
        let Neg::Stack { inner, weight } = types.neg(*upper) else {
            panic!(
                "effect row argument upper should be subtractable, got {:?}",
                types.neg(*upper)
            );
        };
        assert!(matches!(types.neg(*inner), Neg::Var(_)));
        let entry = single_stack_entry(weight);
        assert!(weight_has_set_path(weight, entry.id, &expected));
    }

    #[test]
    fn builds_tuple_annotation() {
        assert_eq!(
            build_annotation("my site: (int, float) = 1\n"),
            AnnType::Tuple(vec![
                AnnType::Builtin(BuiltinType::Int),
                AnnType::Builtin(BuiltinType::Float),
            ])
        );
    }

    #[test]
    fn connects_effectful_annotation_with_stacked_inner_lower() {
        let root = parse("type handled\nmy site: [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let handled = lower.modules.type_decls(module, &Name("handled".into()))[0].id;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let value = infer.fresh_type_var();
        let effect = infer.fresh_type_var();

        let subtracts = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_computation(AnnComputationTarget { value, effect }, &ann)
            .expect("annotation constraints should lower");

        assert_eq!(subtracts.len(), 1);
        let expected = type_decl_path(&lower.modules, handled);
        let bounds = infer
            .constraints()
            .bounds()
            .of(effect)
            .expect("effect should receive stacked inner lower bound");
        // 注釈残差は fresh な内側変数として立ち、push 重み付きで effect の下界に入る。
        // effect 自身への self edge は作らない（replay で重みが際限なく合成されるため）。
        assert!(
            bounds.lowers().iter().any(|bound| {
                matches!(infer.constraints().types().pos(bound.pos), Pos::Var(var) if *var != effect)
                    && weight_has_set_path(&bound.weights.left, subtracts[0], &expected)
            }),
            "effect bounds: {:?}",
            bounds
        );
        assert!(
            !bounds.lowers().iter().any(|bound| {
                matches!(infer.constraints().types().pos(bound.pos), Pos::Var(var) if *var == effect)
                    && !bound.weights.is_empty()
            }),
            "effect must not have weighted self edges: {:?}",
            bounds
        );
    }

    #[test]
    fn function_return_effect_annotation_wraps_output_computation_with_stack() {
        let root = parse("type io\ntype handled\nmy site: 'a [io] -> [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let bounds = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound");
        let types = infer.constraints().types();
        let fun = bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { ret_eff, ret, .. } => Some((*ret_eff, *ret)),
                _ => None,
            })
            .expect("function annotation should lower to function bound");

        let subtract = match types.pos(fun.0) {
            Pos::Stack { inner, weight } => {
                assert!(matches!(types.pos(*inner), Pos::Var(_)));
                let entry = single_stack_entry(weight);
                assert_eq!(entry.pops, 0);
                assert_eq!(entry.stack.len(), 1);
                entry.id
            }
            other => panic!("expected stacked return effect, got {other:?}"),
        };
        match types.pos(fun.1) {
            Pos::Stack { inner, weight } => {
                assert!(matches!(types.pos(*inner), Pos::Var(_)));
                assert_pop_only(weight, subtract, 1);
            }
            other => panic!("expected stacked return value, got {other:?}"),
        }
    }

    #[test]
    fn function_arg_effect_annotation_adds_only_lower_row_to_fresh_arg_effect() {
        let root = parse("type io\nmy site: 'a [io] -> 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let types = infer.constraints().types();
        let fun = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound")
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { arg_eff, .. } => Some(*arg_eff),
                _ => None,
            })
            .expect("function annotation should lower to function bound");
        let arg_effect = match types.neg(fun) {
            Neg::Var(var) => *var,
            other => panic!("expected arg effect variable, got {other:?}"),
        };
        let bounds = infer
            .constraints()
            .bounds()
            .of(arg_effect)
            .expect("arg effect should receive row lower bound");

        assert!(
            !bounds
                .uppers()
                .iter()
                .any(|bound| matches!(types.neg(bound.neg), Neg::Row(_, _)))
        );
        assert!(
            bounds.lowers().iter().any(|bound| {
                matches!(types.pos(bound.pos), Pos::Row(items) if !items.is_empty())
            })
        );
    }

    #[test]
    fn function_return_effect_with_tail_uses_fresh_stacked_proxy() {
        let root = parse("type handled\nmy site: 'a -> [handled; 'e] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        let subtracts = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let [subtract] = subtracts.as_slice() else {
            panic!("expected one subtract id, got {subtracts:?}");
        };
        let types = infer.constraints().types();
        let ret_eff = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound")
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { ret_eff, .. } => Some(*ret_eff),
                _ => None,
            })
            .expect("function annotation should lower to function bound");
        let proxy = match types.pos(ret_eff) {
            Pos::Stack { inner, weight } if weight.contains(*subtract) => match types.pos(*inner) {
                Pos::Var(proxy) => *proxy,
                other => panic!("expected proxy variable, got {other:?}"),
            },
            other => panic!("expected stacked return effect, got {other:?}"),
        };

        let proxy_bounds = infer
            .constraints()
            .bounds()
            .of(proxy)
            .expect("proxy should receive tail lower bound");
        assert!(
            proxy_bounds
                .lowers()
                .iter()
                .any(|bound| { matches!(types.pos(bound.pos), Pos::Var(tail) if *tail != proxy) })
        );
    }

    #[test]
    fn computation_connection_does_not_add_weighted_self_edges() {
        let root = parse("type handled\nmy site: 'a -> [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let value = infer.fresh_type_var();
        let effect = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_computation(AnnComputationTarget { value, effect }, &ann)
            .expect("annotation constraints should lower");

        // 重み付き self edge は bounds replay の合成で重みが際限なく育つため作らない。
        for target in [value, effect] {
            let Some(bounds) = infer.constraints().bounds().of(target) else {
                continue;
            };
            assert!(
                !bounds.lowers().iter().any(|bound| {
                    matches!(
                        infer.constraints().types().pos(bound.pos),
                        Pos::Var(var) if *var == target && !bound.weights.is_empty()
                    )
                }),
                "weighted self edge on {target:?}: {bounds:?}"
            );
        }
    }

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(parser::parse_module_to_green(src))
    }

    fn type_decl_path(modules: &ModuleTable, id: TypeDeclId) -> Vec<String> {
        let decl = modules.type_decl_by_id(id).expect("type decl");
        modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect()
    }

    fn single_stack_entry(weight: &StackWeight) -> &poly::types::StackWeightEntry {
        let [entry] = weight.entries() else {
            panic!("expected one stack entry, got {:?}", weight.entries());
        };
        entry
    }

    fn weight_has_set_path(
        weight: &StackWeight,
        subtract: SubtractId,
        expected: &[String],
    ) -> bool {
        weight.entries().iter().any(|entry| {
            entry.id == subtract
                && entry.stack.iter().any(|subtractability| {
                    matches!(
                        subtractability,
                        Subtractability::Set(path, args) if path == expected && args.is_empty()
                    )
                })
        })
    }

    fn assert_pop_only(weight: &StackWeight, subtract: SubtractId, pops: u32) {
        let entry = single_stack_entry(weight);
        assert_eq!(entry.id, subtract);
        assert_eq!(entry.pops, pops);
        assert!(entry.stack.is_empty());
    }

    fn first_type_expr(root: &Cst) -> Cst {
        root.descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation")
    }

    fn ann_var_id(name: &str, id: u32) -> AnnType {
        AnnType::Var(AnnTypeVar {
            id: AnnTypeVarId(id),
            name: name.to_string(),
        })
    }

    fn ann_apply(callee: AnnType, args: Vec<AnnType>) -> AnnType {
        AnnType::Apply {
            callee: Box::new(callee),
            args,
        }
    }

    fn ann_row(items: Vec<AnnType>, tail: Option<(&str, u32)>) -> AnnEffectRow {
        AnnEffectRow {
            items: items.into_iter().map(AnnEffectAtom::Type).collect(),
            tail: tail.map(|(name, id)| AnnTypeVar {
                id: AnnTypeVarId(id),
                name: name.to_string(),
            }),
        }
    }
}
