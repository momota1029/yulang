//! CST binding body / expression を `poly` IR と推論用 computation slot へ落とす。
//!
//! この module は pass2 の小さな入口として、pass1 が採番した `DefId` に body を書き戻しながら、
//! 式 node から `ExprId` と `typing::Computation` を同時に作る。式そのものに型 table は
//! 残さず、lowering 中に必要な value/effect slot だけを `Computation` として返す。
//!
//! 名前参照は `RefId` を発行して `AnalysisSession` の queue に解決結果を渡す。これにより、
//! `poly` への `RefId -> DefId` 書き戻しと SCC edge 追加は、lowering 本体から分離された
//! event routing 側に残る。

mod body;
mod builtin_op;
mod cast_scheme;
mod constructor;
mod control;
mod error;
mod expr;
mod expr_syntax;
mod list_lit;
mod local;
mod name_ref;
mod neg_signature;
mod pattern;
mod record_lit;
mod rule_lit;
mod signature_effect;
mod signature_match;
mod string_lit;

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use rowan::{NodeOrToken, SyntaxNode};
use sources::{LoadedFile, Name, Path, SourceRange};

use poly::dump::DumpLabels;
use poly::expr::{
    CaseArm, CatchArm, Constructor, Def, DefId, Expr, ExprId, Lit, Pat, PatId, PrimitiveOp,
    RecordSpread, RefId, Stmt, Vis,
};
use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, Scheme, StackWeight, SubtractId,
    Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{AnalysisDiagnostic, AnalysisSession, AnalysisWork};
use crate::annotation::{
    AnnBuildError, AnnComputationTarget, AnnConstraintError, AnnConstraintLowerer, AnnSelfAlias,
    AnnType, AnnTypeBuilder, AnnTypeVarId, effect_row_has_wildcard,
};
use crate::builtin_ops::{BuiltinOp, BuiltinOpSig, SigTy, resolve_builtin_op};
use crate::compact::{
    CompactBounds, CompactFun, CompactRoot, CompactSimplification, CompactType,
    compact_pos_surface, compact_role_constraint, compact_type_var,
};
use crate::constraints::TypeLevel;
use crate::generalize::{
    generalize_prepared_compact_root_with_roles, generalize_type_var_with_boundaries,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
    RoleInputOccurrence, RoleInputVariance,
};
use crate::scc::SccInput;
use crate::time::{Duration, Instant};
use crate::typing::{EffectViewId, Typing};
use crate::uses::{LocalDefUse, RefUse, SelectionUse};
use crate::{
    ActMethodDecl, ActOperationDecl, CastDecl, ConstructorPayload, LoadedFileCsts,
    LoadedFilesError, Lower, ModuleChildDecl, ModuleId, ModuleOrder, ModuleTable, ModuleTypeDecl,
    ModuleTypeKind, RoleImplDecl, RoleImplMethodDecl, RoleMethodDecl, SourceSpan,
    SyntheticSubLabelActUse, SyntheticVarActUse, TypeDeclId, TypeFieldMethodDecl, TypeMethodDecl,
    TypeMethodReceiver, append_root_loaded_file_to_lower, binding_type_expr,
    lower_loaded_file_csts_module_map,
};
use body::signature_helpers::*;
use cast_scheme::{CastScheme, build_cast_scheme_from_ann};
use constructor::{
    ConstructorArg, build_constructor_payload_signatures, connect_constructor_arg_signatures,
    connect_constructor_pattern_arg_signatures, constrain_constructor_arg_shapes,
    constructor_payload_arity, declared_constructor_expr_payloads, prepare_constructor_args,
    prepare_constructor_pattern_args,
};
use expr::ExprLowerer;
use expr_syntax::*;
use local::*;
pub use neg_signature::NegSignatureBuildError;
use neg_signature::*;
use signature_match::{builtin_annotation_mismatch, compact_type_matches_signature};
use string_lit::{plain_string_expr_text, plain_string_lit_text};

pub use crate::typing::{BindingFetch, Computation, Evaluation};
pub use body::{
    BodyLowering, BodyLoweringError, BodyLoweringPrefix, BodyLoweringTiming, lower_binding_bodies,
    lower_loaded_files, lower_loaded_files_prefix, lower_root_loaded_file_with_prefix,
};
pub use error::LoweringError;

type Cst = SyntaxNode<YulangLanguage>;
type CstItem = NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>;

/// binding body lowering の出力。
///
/// `session` は body を持つ `poly::Arena` と制約/SCC machine を所有する。
/// `typing` は `DefId -> TypeVar` だけを保持し、式や pattern の永続型 table は作らない。
struct RoleImplLoweringContext {
    role: TypeDeclId,
    target_ann: AnnType,
    input_names: Vec<String>,
    input_signatures: Vec<SignatureType>,
    associated_signatures: Vec<(String, SignatureType)>,
    type_var_bindings: Vec<(String, AnnTypeVarId)>,
    ann_solver_vars: FxHashMap<AnnTypeVarId, TypeVar>,
}

#[derive(Clone)]
struct RoleMethodRequirement {
    signature: SignatureType,
}

struct ResolvedRoleMethodRequirement {
    role_method: DefId,
    role: Vec<String>,
    inputs: Vec<SignatureType>,
    associated: Vec<(String, SignatureType)>,
    signature: SignatureType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NegSignature {
    signature: SignatureType,
}

impl NegSignature {
    fn new(signature: SignatureType) -> Self {
        Self { signature }
    }

    fn as_type(&self) -> &SignatureType {
        &self.signature
    }
}

fn owner_signature_type(owner: TypeDeclId, type_vars: &[String]) -> SignatureType {
    let args = type_vars
        .iter()
        .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
        .collect::<Vec<_>>();
    if args.is_empty() {
        SignatureType::Named(owner)
    } else {
        SignatureType::Apply {
            callee: Box::new(SignatureType::Named(owner)),
            args,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SignatureSelfAlias {
    owner: TypeDeclId,
    type_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureType {
    Builtin(BuiltinType),
    Named(TypeDeclId),
    Var(SignatureVar),
    EffectRow(SignatureEffectRow),
    Effectful {
        eff: SignatureEffectRow,
        ret: Box<SignatureType>,
    },
    Tuple(Vec<SignatureType>),
    Apply {
        callee: Box<SignatureType>,
        args: Vec<SignatureType>,
    },
    Function {
        param: Box<SignatureType>,
        arg_eff: Option<SignatureEffectRow>,
        ret_eff: Option<SignatureEffectRow>,
        ret: Box<SignatureType>,
    },
}

/// Effectful ラッパを剥がして Function の (param, ret) を返す。
fn signature_function_step(sig: &SignatureType) -> Option<(&SignatureType, &SignatureType)> {
    match sig {
        SignatureType::Effectful { ret, .. } => signature_function_step(ret),
        SignatureType::Function { param, ret, .. } => Some((param.as_ref(), ret.as_ref())),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureEffectRow {
    items: Vec<SignatureEffectAtom>,
    tail: Option<SignatureVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SignatureEffectStack {
    weight: StackWeight,
    ids: Vec<SubtractId>,
}

impl SignatureEffectStack {
    fn empty() -> Self {
        Self {
            weight: StackWeight::empty(),
            ids: Vec::new(),
        }
    }
}

fn signature_subtractability_from_atoms(atoms: Vec<(Vec<String>, Vec<NeuId>)>) -> Subtractability {
    match atoms.as_slice() {
        [] => Subtractability::Empty,
        [(path, args)] => Subtractability::Set(path.clone(), args.clone()),
        _ => Subtractability::SetMany(atoms),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureEffectAtom {
    Type(SignatureType),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureVar {
    name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureShape {
    Any,
    Constructor,
    EffectRow,
    Function,
    Tuple,
}

impl SignatureShape {
    fn of(signature: &SignatureType) -> Self {
        match signature {
            SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
                Self::Constructor
            }
            SignatureType::EffectRow(_) => Self::EffectRow,
            SignatureType::Effectful { ret, .. } => Self::of(ret),
            SignatureType::Tuple(_) => Self::Tuple,
            SignatureType::Function { .. } => Self::Function,
            SignatureType::Var(_) => Self::Any,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureConstraintError {
    MissingTypeDecl { id: TypeDeclId },
    InvalidConstructorCallee { ty: SignatureType },
    WildcardEffectRowInTypePosition,
}

struct SignatureLowerer<'a> {
    infer: &'a mut crate::Arena,
    modules: &'a ModuleTable,
    vars: FxHashMap<String, TypeVar>,
    new_var_level: Option<TypeLevel>,
}

impl<'a> SignatureLowerer<'a> {
    fn new(infer: &'a mut crate::Arena, modules: &'a ModuleTable) -> Self {
        Self {
            infer,
            modules,
            vars: FxHashMap::default(),
            new_var_level: None,
        }
    }

    fn with_vars(
        infer: &'a mut crate::Arena,
        modules: &'a ModuleTable,
        vars: FxHashMap<String, TypeVar>,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: None,
        }
    }

    fn with_vars_at_level(
        infer: &'a mut crate::Arena,
        modules: &'a ModuleTable,
        vars: FxHashMap<String, TypeVar>,
        new_var_level: TypeLevel,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: Some(new_var_level),
        }
    }

    fn lower_role_arg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<RoleConstraintArg, SignatureConstraintError> {
        Ok(RoleConstraintArg {
            lower: self.lower_pos(signature)?,
            upper: self.lower_neg(signature)?,
        })
    }

    fn lower_pos(&mut self, signature: &SignatureType) -> Result<PosId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_pos(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_pos(Pos::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_pos(Pos::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_effect_row_pos(row),
            SignatureType::Effectful { ret, .. } => self.lower_pos(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_pos(Pos::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_pos(Pos::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_neg(param)?;
                let arg_eff = self.lower_arg_effect_neg(arg_eff.as_ref())?;
                let ret_eff = self.lower_ret_effect_pos(ret_eff.as_ref())?;
                let ret = self.lower_pos(ret)?;
                Ok(self.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_neg(&mut self, signature: &SignatureType) -> Result<NegId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_neg(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_neg(Neg::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_neg(Neg::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_subtractable_effect_row_neg(row),
            SignatureType::Effectful { ret, .. } => self.lower_neg(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_neg(Neg::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_neg(Neg::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_pos(param)?;
                let arg_eff = self.lower_arg_effect_pos(arg_eff.as_ref())?;
                let ret_eff = self.lower_ret_effect_neg(ret_eff.as_ref())?;
                let ret = self.lower_neg(ret)?;
                Ok(self.alloc_neg(Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_data_neg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<NegId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_neg(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_neg(Neg::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_neg(Neg::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_effect_row_neg(row),
            SignatureType::Effectful { ret, .. } => self.lower_data_neg(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_data_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_neg(Neg::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_neg(Neg::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_pos(param)?;
                let arg_eff = self.lower_arg_effect_pos(arg_eff.as_ref())?;
                let ret_eff = self.lower_data_ret_effect_neg(ret_eff.as_ref())?;
                let ret = self.lower_data_neg(ret)?;
                Ok(self.alloc_neg(Neg::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_data_pos(
        &mut self,
        signature: &SignatureType,
    ) -> Result<PosId, SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => Ok(self.lower_builtin_pos(*builtin)),
            SignatureType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.alloc_pos(Pos::Con(path, Vec::new())))
            }
            SignatureType::Var(var) => {
                let var = self.signature_var(var);
                Ok(self.alloc_pos(Pos::Var(var)))
            }
            SignatureType::EffectRow(row) => self.lower_data_effect_row_pos(row),
            SignatureType::Effectful { ret, .. } => self.lower_data_pos(ret),
            SignatureType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_data_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.alloc_pos(Pos::Tuple(items)))
            }
            SignatureType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(self.alloc_pos(Pos::Con(path, neu_args)))
            }
            SignatureType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.lower_data_neg(param)?;
                let arg_eff = self.lower_arg_effect_neg(arg_eff.as_ref())?;
                let ret_eff = self.lower_data_ret_effect_pos(ret_eff.as_ref())?;
                let ret = self.lower_data_pos(ret)?;
                Ok(self.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    fn lower_invariant_arg(
        &mut self,
        signature: &SignatureType,
    ) -> Result<NeuId, SignatureConstraintError> {
        let lower = self.lower_pos(signature)?;
        let upper = self.lower_neg(signature)?;
        Ok(self.alloc_neu(Neu::Bounds(lower, upper)))
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
        signature: &SignatureType,
    ) -> Result<(Vec<String>, Vec<NeuId>), SignatureConstraintError> {
        match signature {
            SignatureType::Builtin(builtin) => {
                Ok((vec![builtin.surface_name().to_string()], Vec::new()))
            }
            SignatureType::Named(id) => Ok((self.type_decl_path(*id)?, Vec::new())),
            SignatureType::Apply { callee, args } => {
                let (path, mut head_args) = self.constructor_path(callee)?;
                for arg in args {
                    head_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok((path, head_args))
            }
            ty => Err(SignatureConstraintError::InvalidConstructorCallee { ty: ty.clone() }),
        }
    }

    fn type_decl_path(&mut self, id: TypeDeclId) -> Result<Vec<String>, SignatureConstraintError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(SignatureConstraintError::MissingTypeDecl { id })?;
        let path = self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        if decl.kind == ModuleTypeKind::Act {
            self.infer.register_effect_family_path(path.clone());
        }
        Ok(path)
    }

    fn signature_var(&mut self, var: &SignatureVar) -> TypeVar {
        if let Some(found) = self.vars.get(&var.name) {
            return *found;
        }
        let ty = self.fresh_type_var();
        self.vars.insert(var.name.clone(), ty);
        ty
    }

    fn fresh_type_var(&mut self) -> TypeVar {
        if let Some(level) = self.new_var_level {
            self.infer.fresh_type_var_at(level)
        } else {
            self.infer.fresh_type_var()
        }
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

struct RoleImplAnnSpec {
    role: TypeDeclId,
    target: AnnType,
    inputs: Vec<AnnType>,
}

fn role_impl_ann_spec(
    modules: &ModuleTable,
    head: AnnType,
    description: Option<AnnType>,
    attached_target: Option<AnnType>,
) -> Option<RoleImplAnnSpec> {
    if let Some(description) = description {
        let (role, mut inputs) = role_ann_application(modules, description)?;
        let mut all_inputs = Vec::with_capacity(inputs.len() + 1);
        all_inputs.push(head.clone());
        all_inputs.append(&mut inputs);
        return Some(RoleImplAnnSpec {
            role,
            target: head,
            inputs: all_inputs,
        });
    }

    let (role, mut inputs) = role_ann_application(modules, head.clone())?;
    if let Some(attached_target) = attached_target {
        let mut all_inputs = Vec::with_capacity(inputs.len() + 1);
        all_inputs.push(attached_target.clone());
        all_inputs.append(&mut inputs);
        return Some(RoleImplAnnSpec {
            role,
            target: attached_target,
            inputs: all_inputs,
        });
    }
    let target = inputs.first().cloned().unwrap_or(head);
    Some(RoleImplAnnSpec {
        role,
        target,
        inputs,
    })
}

fn role_ann_application(modules: &ModuleTable, ann: AnnType) -> Option<(TypeDeclId, Vec<AnnType>)> {
    match ann {
        AnnType::Named(id) if ann_type_is_role(modules, id) => Some((id, Vec::new())),
        AnnType::Apply { callee, args } => match *callee {
            AnnType::Named(id) if ann_type_is_role(modules, id) => Some((id, args)),
            _ => None,
        },
        _ => None,
    }
}

fn ann_type_is_role(modules: &ModuleTable, id: TypeDeclId) -> bool {
    modules
        .type_decl_by_id(id)
        .is_some_and(|decl| decl.kind == ModuleTypeKind::Role)
}

fn substitute_role_requirement_signature(
    requirement: &RoleMethodRequirement,
    context: &RoleImplLoweringContext,
) -> SignatureType {
    let substitutions = context
        .input_names
        .iter()
        .cloned()
        .zip(context.input_signatures.iter().cloned())
        .chain(context.associated_signatures.iter().cloned())
        .collect::<FxHashMap<_, _>>();
    substitute_signature_vars(&requirement.signature, &substitutions)
}

fn lower_impl_requirement_role_constraint(
    lowerer: &mut SignatureLowerer<'_>,
    requirement: &ResolvedRoleMethodRequirement,
) -> Result<RoleConstraint, LoweringError> {
    let inputs = requirement
        .inputs
        .iter()
        .map(|signature| {
            lowerer
                .lower_role_arg(signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let associated = requirement
        .associated
        .iter()
        .map(|(name, signature)| {
            lowerer
                .lower_role_arg(signature)
                .map(|value| RoleAssociatedConstraint {
                    name: name.clone(),
                    value,
                })
                .map_err(|error| LoweringError::SignatureConstraint { error })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(RoleConstraint {
        role: requirement.role.clone(),
        inputs,
        associated,
    })
}

fn substitute_signature_vars(
    signature: &SignatureType,
    substitutions: &FxHashMap<String, SignatureType>,
) -> SignatureType {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Named(_) => signature.clone(),
        SignatureType::Var(var) => substitutions
            .get(&var.name)
            .cloned()
            .unwrap_or_else(|| signature.clone()),
        SignatureType::EffectRow(row) => {
            SignatureType::EffectRow(substitute_signature_effect_row(row, substitutions))
        }
        SignatureType::Effectful { eff, ret } => SignatureType::Effectful {
            eff: substitute_signature_effect_row(eff, substitutions),
            ret: Box::new(substitute_signature_vars(ret, substitutions)),
        },
        SignatureType::Tuple(items) => SignatureType::Tuple(
            items
                .iter()
                .map(|item| substitute_signature_vars(item, substitutions))
                .collect(),
        ),
        SignatureType::Apply { callee, args } => SignatureType::Apply {
            callee: Box::new(substitute_signature_vars(callee, substitutions)),
            args: args
                .iter()
                .map(|arg| substitute_signature_vars(arg, substitutions))
                .collect(),
        },
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => SignatureType::Function {
            param: Box::new(substitute_signature_vars(param, substitutions)),
            arg_eff: arg_eff
                .as_ref()
                .map(|row| substitute_signature_effect_row(row, substitutions)),
            ret_eff: ret_eff
                .as_ref()
                .map(|row| substitute_signature_effect_row(row, substitutions)),
            ret: Box::new(substitute_signature_vars(ret, substitutions)),
        },
    }
}

fn substitute_signature_effect_row(
    row: &SignatureEffectRow,
    substitutions: &FxHashMap<String, SignatureType>,
) -> SignatureEffectRow {
    SignatureEffectRow {
        items: row
            .items
            .iter()
            .map(|atom| match atom {
                SignatureEffectAtom::Type(ty) => {
                    SignatureEffectAtom::Type(substitute_signature_vars(ty, substitutions))
                }
                SignatureEffectAtom::Wildcard => SignatureEffectAtom::Wildcard,
            })
            .collect(),
        tail: row
            .tail
            .as_ref()
            .map(|tail| match substitutions.get(&tail.name) {
                Some(SignatureType::Var(var)) => var.clone(),
                _ => tail.clone(),
            }),
    }
}

fn signature_vars_from_ann_vars(
    bindings: &[(String, AnnTypeVarId)],
    vars: &FxHashMap<AnnTypeVarId, TypeVar>,
) -> FxHashMap<String, TypeVar> {
    bindings
        .iter()
        .filter_map(|(name, id)| vars.get(id).copied().map(|var| (name.clone(), var)))
        .collect()
}

fn impl_head_type_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

fn impl_description_type_expr(node: &Cst) -> Option<Cst> {
    crate::child_node(node, SyntaxKind::ImplDescription)?
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

fn role_impl_associated_type_exprs(node: &Cst) -> FxHashMap<String, Cst> {
    let mut out = FxHashMap::default();
    collect_role_impl_associated_type_exprs(node, &mut out);
    out
}

fn collect_role_impl_associated_type_exprs(node: &Cst, out: &mut FxHashMap<String, Cst>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                collect_role_impl_associated_type_exprs(&child, out);
            }
            SyntaxKind::TypeDecl => {
                let Some(name) = crate::type_decl_name(&child) else {
                    continue;
                };
                let Some(type_expr) = type_decl_rhs_type_expr(&child) else {
                    continue;
                };
                out.insert(name.0, type_expr);
            }
            _ => {}
        }
    }
}

fn type_decl_rhs_type_expr(node: &Cst) -> Option<Cst> {
    let mut after_equal = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Equal => {
                after_equal = true;
            }
            NodeOrToken::Node(child) if after_equal && child.kind() == SyntaxKind::TypeExpr => {
                return Some(child);
            }
            NodeOrToken::Node(child)
                if after_equal
                    && matches!(
                        child.kind(),
                        SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                    ) =>
            {
                return child
                    .children()
                    .find(|child| child.kind() == SyntaxKind::TypeExpr);
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests;
