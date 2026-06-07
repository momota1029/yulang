use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_erased_ir as erased;
use yulang_typed_ir as typed_ir;

use crate::ast::expr::{
    CatchArmKind, ExprKind, Lit as LowerLit, PatKind, RecordPatSpread, RecordSpread, TypedBlock,
    TypedCatchArm, TypedExpr, TypedPat, TypedStmt,
};
use crate::ids::{DefId, RefId, TypeVar};
use crate::lower::LowerState;
use crate::symbols::{Name, Path};

use super::names::path_key;
use super::spine::{collect_apply_spine, strip_transparent_wrappers};
use super::types::{export_frozen_scheme, export_scheme, export_type_bounds_for_tv};

pub fn export_erased_program(state: &mut LowerState) -> erased::InferExport {
    state.refresh_selection_environment();
    let binding_paths = state.ctx.collect_all_binding_paths();
    let target_defs = collect_erased_target_defs(state, &binding_paths);
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment_for_owner_defs(&target_defs);

    let globals = binding_paths
        .iter()
        .cloned()
        .map(|(path, def)| (def, path))
        .collect::<HashMap<_, _>>();
    let selected_paths = binding_paths
        .iter()
        .filter(|(_, def)| target_defs.contains(def))
        .cloned()
        .collect::<Vec<_>>();

    let mut exporter = ErasedExporter::new(state, globals);
    let root_exprs = exporter.export_root_exprs();
    let bindings = exporter.export_bindings(&selected_paths);
    let roots = (0..root_exprs.len())
        .map(erased::PrincipalRoot::Expr)
        .collect();

    erased::InferExport {
        erased: erased::ErasedProgram {
            module: erased::ErasedModule {
                path: erased::Path::default(),
                bindings,
                root_exprs,
                roots,
            },
            refs: exporter.refs,
        },
    }
}

fn collect_erased_target_defs(
    state: &LowerState,
    binding_paths: &[(Path, DefId)],
) -> HashSet<DefId> {
    let mut target_defs = binding_paths
        .iter()
        .map(|(_, def)| *def)
        .collect::<HashSet<_>>();
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    target_defs.extend(state.internal_expr_owners.iter().copied());
    target_defs
}

struct ErasedExporter<'a> {
    state: &'a LowerState,
    globals: HashMap<DefId, Path>,
    local_defs: Vec<DefId>,
    current_binding: Option<DefId>,
    pending_typeclass_obligations: HashMap<DefId, Vec<erased::TypeClassObligation>>,
    refs: erased::RefExportTable,
}

impl<'a> ErasedExporter<'a> {
    fn new(state: &'a LowerState, globals: HashMap<DefId, Path>) -> Self {
        Self {
            state,
            globals,
            local_defs: Vec::new(),
            current_binding: None,
            pending_typeclass_obligations: HashMap::new(),
            refs: erased::RefExportTable::default(),
        }
    }

    fn export_bindings(
        &mut self,
        selected_paths: &[(Path, DefId)],
    ) -> Vec<erased::InferredBinding> {
        let mut paths = selected_paths.to_vec();
        paths.sort_by(|(lhs, _), (rhs, _)| path_key(lhs).cmp(&path_key(rhs)));
        paths
            .into_iter()
            .filter_map(|(path, def)| self.export_binding(&path, def))
            .collect()
    }

    fn export_binding(&mut self, path: &Path, def: DefId) -> Option<erased::InferredBinding> {
        let body = self.state.principal_bodies.get(&def)?;
        let body = self.with_current_binding(def, |this| this.export_inferred_expr(body));
        let scheme = self.export_scheme(def);
        Some(erased::InferredBinding {
            name: export_path(path),
            scheme,
            body,
        })
    }

    fn export_root_exprs(&mut self) -> Vec<erased::InferredExpr> {
        let owner_roots = self.export_owner_root_exprs();
        if !owner_roots.is_empty() {
            return owner_roots;
        }

        let mut roots = Vec::new();
        for (path, block) in &self.state.top_level_blocks {
            if !path.segments.is_empty() {
                continue;
            }
            for stmt in &block.stmts {
                if let TypedStmt::Expr(expr) = stmt {
                    roots.push(self.export_inferred_expr(expr));
                }
            }
            if let Some(tail) = &block.tail {
                roots.push(self.export_inferred_expr(tail));
            }
        }
        roots
    }

    fn export_owner_root_exprs(&mut self) -> Vec<erased::InferredExpr> {
        let mut roots = Vec::new();
        for owner in &self.state.top_level_expr_owners {
            let Some(body) = self.state.principal_bodies.get(owner) else {
                continue;
            };
            roots.push(self.export_inferred_expr(body));
        }
        roots
    }

    fn export_inferred_expr(&mut self, expr: &TypedExpr) -> erased::InferredExpr {
        erased::InferredExpr {
            typ: convert_type_bounds(export_type_bounds_for_tv(&self.state.infer, expr.tv)),
            eff: convert_type_bounds(export_type_bounds_for_tv(&self.state.infer, expr.eff)),
            ir: self.export_expr(expr),
        }
    }

    fn export_expr(&mut self, expr: &TypedExpr) -> erased::ErasedExpr {
        if let Some(expr) = self.export_role_method_call(expr) {
            return expr;
        }
        match &expr.kind {
            ExprKind::PrimitiveOp(op) => erased::ErasedExpr::PrimitiveOp(convert_primitive_op(*op)),
            ExprKind::Lit(lit) => erased::ErasedExpr::Lit(export_lit(lit)),
            ExprKind::Var(def) => self.export_def_use(*def),
            ExprKind::Ref(ref_id) => self.export_ref_use(*ref_id),
            ExprKind::App { callee, arg, .. } => erased::ErasedExpr::Apply {
                callee: Box::new(self.export_expr(callee)),
                arg: Box::new(self.export_expr(arg)),
            },
            ExprKind::RefSet { reference, value } => erased::ErasedExpr::RefSet {
                reference: Box::new(self.export_expr(reference)),
                value: Box::new(self.export_expr(value)),
            },
            ExprKind::Lam(def, body) => self.with_local(*def, |this| erased::ErasedExpr::Lambda {
                param: export_def_id(*def),
                body: Box::new(this.export_expr(body)),
            }),
            ExprKind::Tuple(items) => {
                erased::ErasedExpr::Tuple(items.iter().map(|item| self.export_expr(item)).collect())
            }
            ExprKind::Record { fields, spread } => erased::ErasedExpr::Record {
                fields: fields
                    .iter()
                    .map(|(name, value)| erased::RecordExprField {
                        name: export_name(name),
                        value: self.export_expr(value),
                    })
                    .collect(),
                spread: spread.as_ref().map(|spread| match spread {
                    RecordSpread::Head(expr) => {
                        erased::RecordSpreadExpr::Head(Box::new(self.export_expr(expr)))
                    }
                    RecordSpread::Tail(expr) => {
                        erased::RecordSpreadExpr::Tail(Box::new(self.export_expr(expr)))
                    }
                }),
            },
            ExprKind::PolyVariant(name, payloads, origin) => erased::ErasedExpr::Variant {
                tag: export_name(name),
                value: self.export_variant_expr_payload(payloads),
                source: match origin {
                    crate::ast::expr::PolyVariantOrigin::Syntax => {
                        erased::VariantExprSource::PolyVariantSyntax
                    }
                    crate::ast::expr::PolyVariantOrigin::Constructor => {
                        erased::VariantExprSource::Constructor
                    }
                },
            },
            ExprKind::Select { recv, name } => erased::ErasedExpr::Select {
                base: Box::new(self.export_expr(recv)),
                field: export_name(name),
            },
            ExprKind::Match(scrutinee, arms) => erased::ErasedExpr::Match {
                scrutinee: Box::new(self.export_expr(scrutinee)),
                arms: arms
                    .iter()
                    .map(|arm| {
                        self.with_pattern_scope(&arm.pat, |this| erased::MatchArm {
                            pattern: this.export_pat(&arm.pat),
                            guard: arm.guard.as_ref().map(|guard| this.export_expr(guard)),
                            body: this.export_expr(&arm.body),
                        })
                    })
                    .collect(),
            },
            ExprKind::Catch(body, arms) => erased::ErasedExpr::Handle {
                body: Box::new(self.export_expr(body)),
                arms: arms.iter().map(|arm| self.export_catch_arm(arm)).collect(),
            },
            ExprKind::Block(block) => erased::ErasedExpr::Block(self.export_block(block)),
            ExprKind::BindHere(expr) => erased::ErasedExpr::BindHere {
                expr: Box::new(self.export_expr(expr)),
            },
            ExprKind::Coerce { expr, .. } => self.export_expr(expr),
            ExprKind::PackForall(var, expr) => erased::ErasedExpr::Pack {
                var: erased::TypeVar(format!("t{}", var.0)),
                expr: Box::new(self.export_expr(expr)),
            },
        }
    }

    fn export_role_method_call(&mut self, expr: &TypedExpr) -> Option<erased::ErasedExpr> {
        let (head, args) = collect_apply_spine(expr);
        let head = strip_transparent_wrappers(head);
        match &head.kind {
            ExprKind::Select { recv, .. } => {
                let ref_id = self
                    .role_method_call_ref(expr.tv)
                    .or_else(|| self.role_method_call_ref(head.tv))?;
                let mut lowered = erased::ErasedExpr::Ref(ref_id);
                lowered = erased::ErasedExpr::Apply {
                    callee: Box::new(lowered),
                    arg: Box::new(self.export_expr(recv)),
                };
                for arg in args {
                    lowered = erased::ErasedExpr::Apply {
                        callee: Box::new(lowered),
                        arg: Box::new(self.export_expr(arg)),
                    };
                }
                Some(lowered)
            }
            ExprKind::Var(_) | ExprKind::Ref(_) => {
                let ref_id = self.role_method_call_ref(expr.tv)?;
                let mut lowered = erased::ErasedExpr::Ref(ref_id);
                for arg in args {
                    lowered = erased::ErasedExpr::Apply {
                        callee: Box::new(lowered),
                        arg: Box::new(self.export_expr(arg)),
                    };
                }
                Some(lowered)
            }
            _ => None,
        }
    }

    fn role_method_call_ref(&mut self, result_tv: TypeVar) -> Option<erased::RefId> {
        if let Some(selection) = self.state.infer.resolved_role_method_selection(result_tv) {
            return Some(self.register_resolved_role_method_ref(selection));
        }
        let selection = self.state.infer.role_method_call_selection(result_tv)?;
        self.register_unresolved_role_method_ref(selection)
    }

    fn export_block(&mut self, block: &TypedBlock) -> erased::ErasedBlock {
        erased::ErasedBlock {
            stmts: block
                .stmts
                .iter()
                .map(|stmt| self.export_stmt(stmt))
                .collect(),
            tail: block
                .tail
                .as_ref()
                .map(|tail| Box::new(self.export_expr(tail))),
        }
    }

    fn export_stmt(&mut self, stmt: &TypedStmt) -> erased::ErasedStmt {
        match stmt {
            TypedStmt::Let(pattern, value) => {
                let value = self.export_expr(value);
                let pattern = self.with_pattern_scope(pattern, |this| this.export_pat(pattern));
                erased::ErasedStmt::Let { pattern, value }
            }
            TypedStmt::Expr(expr) => erased::ErasedStmt::Expr(self.export_expr(expr)),
            TypedStmt::Module(def, body) => erased::ErasedStmt::Module {
                def: export_def_id(*def),
                body: self.export_block(body),
            },
        }
    }

    fn export_catch_arm(&mut self, arm: &TypedCatchArm) -> erased::HandleArm {
        match &arm.kind {
            CatchArmKind::Value(pattern, body) => {
                self.with_pattern_scope(pattern, |this| erased::HandleArm {
                    effect: erased::Path::default(),
                    payload: this.export_pat(pattern),
                    resume: None,
                    guard: arm.guard.as_ref().map(|guard| this.export_expr(guard)),
                    body: this.export_expr(body),
                })
            }
            CatchArmKind::Effect {
                op_path,
                pat,
                k,
                body,
            } => self.with_local(*k, |this| {
                this.with_pattern_scope(pat, |this| erased::HandleArm {
                    effect: export_path(op_path),
                    payload: this.export_pat(pat),
                    resume: Some(export_def_id(*k)),
                    guard: arm.guard.as_ref().map(|guard| this.export_expr(guard)),
                    body: this.export_expr(body),
                })
            }),
        }
    }

    fn export_pat(&mut self, pat: &TypedPat) -> erased::Pattern {
        match &pat.kind {
            PatKind::Wild => erased::Pattern::Wildcard,
            PatKind::Lit(lit) => erased::Pattern::Lit(export_lit(lit)),
            PatKind::Tuple(items) => {
                erased::Pattern::Tuple(items.iter().map(|item| self.export_pat(item)).collect())
            }
            PatKind::List {
                prefix,
                spread,
                suffix,
            } => erased::Pattern::List {
                prefix: prefix.iter().map(|item| self.export_pat(item)).collect(),
                spread: spread
                    .as_ref()
                    .map(|spread| Box::new(self.export_pat(spread))),
                suffix: suffix.iter().map(|item| self.export_pat(item)).collect(),
            },
            PatKind::Record { spread, fields } => erased::Pattern::Record {
                fields: fields
                    .iter()
                    .map(|field| erased::RecordPatternField {
                        name: export_name(&field.name),
                        pattern: self.export_pat(&field.pat),
                        default: field
                            .default
                            .as_ref()
                            .map(|default| self.export_expr(default)),
                    })
                    .collect(),
                spread: spread.as_ref().map(|spread| match spread {
                    RecordPatSpread::Head(pat) => {
                        erased::RecordSpreadPattern::Head(Box::new(self.export_pat(pat)))
                    }
                    RecordPatSpread::Tail(pat) => {
                        erased::RecordSpreadPattern::Tail(Box::new(self.export_pat(pat)))
                    }
                }),
            },
            PatKind::PolyVariant(name, items) => erased::Pattern::Variant {
                tag: export_name(name),
                value: self.export_variant_pattern_payload(items),
            },
            PatKind::Con(ref_id, payload) => {
                self.ensure_existing_ref(*ref_id);
                erased::Pattern::Constructor {
                    ref_id: export_ref_id(*ref_id),
                    payload: payload
                        .as_ref()
                        .map(|payload| Box::new(self.export_pat(payload))),
                }
            }
            PatKind::UnresolvedName(name) => self
                .state
                .ctx
                .resolve_bound_value(name)
                .map(export_def_id)
                .map(erased::Pattern::Bind)
                .unwrap_or_else(|| erased::Pattern::UnresolvedName(export_name(name))),
            PatKind::Or(lhs, rhs) => erased::Pattern::Or {
                left: Box::new(self.export_pat(lhs)),
                right: Box::new(self.export_pat(rhs)),
            },
            PatKind::As(pattern, def) if matches!(pattern.kind, PatKind::Wild) => {
                erased::Pattern::Bind(export_def_id(*def))
            }
            PatKind::As(pattern, def) => erased::Pattern::As {
                pattern: Box::new(self.export_pat(pattern)),
                def: export_def_id(*def),
            },
        }
    }

    fn export_variant_expr_payload(
        &mut self,
        payloads: &[TypedExpr],
    ) -> Option<Box<erased::ErasedExpr>> {
        match payloads {
            [] => None,
            [payload] => Some(Box::new(self.export_expr(payload))),
            payloads => Some(Box::new(erased::ErasedExpr::Tuple(
                payloads
                    .iter()
                    .map(|payload| self.export_expr(payload))
                    .collect(),
            ))),
        }
    }

    fn export_variant_pattern_payload(
        &mut self,
        payloads: &[TypedPat],
    ) -> Option<Box<erased::Pattern>> {
        match payloads {
            [] => None,
            [payload] => Some(Box::new(self.export_pat(payload))),
            payloads => Some(Box::new(erased::Pattern::Tuple(
                payloads
                    .iter()
                    .map(|payload| self.export_pat(payload))
                    .collect(),
            ))),
        }
    }

    fn export_def_use(&mut self, def: DefId) -> erased::ErasedExpr {
        if self.is_local_def(def) || !self.globals.contains_key(&def) {
            return erased::ErasedExpr::Def(export_def_id(def));
        }
        let ref_id = crate::ids::fresh_ref_id();
        self.refs
            .direct
            .insert(export_ref_id(ref_id), export_def_id(def));
        erased::ErasedExpr::Ref(export_ref_id(ref_id))
    }

    fn export_ref_use(&mut self, ref_id: RefId) -> erased::ErasedExpr {
        self.ensure_existing_ref(ref_id);
        erased::ErasedExpr::Ref(export_ref_id(ref_id))
    }

    fn register_resolved_role_method_ref(
        &mut self,
        selection: crate::solve::ResolvedRoleMethodSelection,
    ) -> erased::RefId {
        let ref_id = crate::ids::fresh_ref_id();
        let erased_ref = export_ref_id(ref_id);
        self.refs.resolved_typeclass.insert(
            erased_ref,
            erased::ResolvedTypeClassRef {
                class: export_path(&selection.role),
                member: export_def_id(selection.member),
                impl_def: self
                    .state
                    .def_owner(selection.impl_member)
                    .map(export_def_id),
                impl_member: export_def_id(selection.impl_member),
            },
        );
        erased_ref
    }

    fn register_unresolved_role_method_ref(
        &mut self,
        selection: crate::solve::RoleMethodCallSelection,
    ) -> Option<erased::RefId> {
        let owner = self.current_binding?;
        let ref_id = crate::ids::fresh_ref_id();
        let erased_ref = export_ref_id(ref_id);
        let obligation = self.typeclass_obligation_for_selection(erased_ref, selection)?;
        self.pending_typeclass_obligations
            .entry(owner)
            .or_default()
            .push(obligation);
        Some(erased_ref)
    }

    fn typeclass_obligation_for_selection(
        &self,
        ref_id: erased::RefId,
        selection: crate::solve::RoleMethodCallSelection,
    ) -> Option<erased::TypeClassObligation> {
        let info = self
            .state
            .infer
            .role_method_info_for_def(selection.member)?;
        let arg_infos = self.state.infer.role_arg_infos_of(&selection.role);
        let input_map = role_method_input_tv_map_for_export(
            &info,
            &arg_infos,
            Some(selection.recv_tv),
            &selection.arg_tvs,
        )?;
        let mut args = Vec::new();
        let mut associated = Vec::new();
        for arg_info in arg_infos {
            if arg_info.is_input {
                let tvs = input_map.get(&arg_info.name)?;
                args.push(self.export_typeclass_input_arg(tvs));
            } else if info.output_name.as_deref() == Some(arg_info.name.as_str()) {
                associated.push(erased::AssociatedTypeConstraint {
                    name: erased::Name(arg_info.name),
                    bounds: convert_type_bounds(export_type_bounds_for_tv(
                        &self.state.infer,
                        selection.result_tv,
                    )),
                });
            }
        }
        Some(erased::TypeClassObligation {
            ref_id,
            class: export_path(&selection.role),
            member: export_def_id(selection.member),
            args,
            associated,
        })
    }

    fn export_typeclass_input_arg(&self, tvs: &[TypeVar]) -> erased::Type {
        let mut items = tvs
            .iter()
            .copied()
            .map(|tv| {
                type_from_bounds(convert_type_bounds(export_type_bounds_for_tv(
                    &self.state.infer,
                    tv,
                )))
            })
            .collect::<Vec<_>>();
        items.dedup();
        match items.as_slice() {
            [] => erased::Type::Unknown,
            [item] => item.clone(),
            _ => erased::Type::Union(items),
        }
    }

    fn ensure_existing_ref(&mut self, ref_id: RefId) {
        if let Some(def) = self.state.ctx.refs.get(ref_id) {
            self.refs
                .direct
                .entry(export_ref_id(ref_id))
                .or_insert_with(|| export_def_id(def));
        }
    }

    fn export_scheme(&mut self, def: DefId) -> erased::Scheme {
        let frozen = self.state.infer.frozen_scheme_of(def);
        let quantified_types = frozen
            .as_ref()
            .map(|scheme| {
                scheme
                    .quantified
                    .iter()
                    .copied()
                    .map(export_type_var)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        if let Some(scheme) = self.state.runtime_export_schemes.get(&def) {
            let mut scheme = convert_scheme(scheme.clone(), quantified_types);
            self.attach_pending_typeclass_obligations(def, &mut scheme);
            return scheme;
        }
        if let Some(scheme) = self.state.compact_scheme_of(def) {
            let constraints = self.state.infer.compact_role_constraints_of(def);
            let scheme = export_scheme(&self.state.infer, &scheme, &constraints);
            let mut scheme = convert_scheme_with_fallback_quantified(scheme, quantified_types);
            self.attach_pending_typeclass_obligations(def, &mut scheme);
            return scheme;
        }
        if let Some(frozen) = frozen {
            let quantified_types = frozen
                .quantified
                .iter()
                .copied()
                .map(export_type_var)
                .collect::<Vec<_>>();
            let scheme = export_frozen_scheme(&self.state.infer, &frozen);
            let mut scheme = convert_scheme(scheme, quantified_types);
            self.attach_pending_typeclass_obligations(def, &mut scheme);
            return scheme;
        }
        let mut scheme = erased::Scheme {
            body: erased::Type::Unknown,
            quantified_types: Vec::new(),
            quantified_effects: Vec::new(),
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: Vec::new(),
        };
        self.attach_pending_typeclass_obligations(def, &mut scheme);
        scheme
    }

    fn attach_pending_typeclass_obligations(&mut self, def: DefId, scheme: &mut erased::Scheme) {
        let Some(obligations) = self.pending_typeclass_obligations.remove(&def) else {
            return;
        };
        for obligation in obligations {
            if !scheme.quantified_refs.contains(&obligation.ref_id) {
                scheme.quantified_refs.push(obligation.ref_id);
            }
            if !scheme.typeclass_obligations.contains(&obligation) {
                scheme.typeclass_obligations.push(obligation);
            }
        }
    }

    fn with_current_binding<T>(&mut self, def: DefId, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous = self.current_binding.replace(def);
        let out = f(self);
        self.current_binding = previous;
        out
    }

    fn with_local<T>(&mut self, def: DefId, f: impl FnOnce(&mut Self) -> T) -> T {
        let old_len = self.local_defs.len();
        self.local_defs.push(def);
        if let Some(local_defs) = self.state.lambda_local_defs.get(&def) {
            self.local_defs.extend(local_defs.iter().copied());
        }
        let out = f(self);
        self.local_defs.truncate(old_len);
        out
    }

    fn with_pattern_scope<T>(&mut self, pat: &TypedPat, f: impl FnOnce(&mut Self) -> T) -> T {
        let old_len = self.local_defs.len();
        collect_pattern_local_defs(pat, &mut self.local_defs);
        let out = f(self);
        self.local_defs.truncate(old_len);
        out
    }

    fn is_local_def(&self, def: DefId) -> bool {
        self.local_defs.contains(&def)
    }
}

fn collect_pattern_local_defs(pat: &TypedPat, out: &mut Vec<DefId>) {
    match &pat.kind {
        PatKind::Tuple(items) | PatKind::PolyVariant(_, items) => {
            for item in items {
                collect_pattern_local_defs(item, out);
            }
        }
        PatKind::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_pattern_local_defs(item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_local_defs(spread, out);
            }
            for item in suffix {
                collect_pattern_local_defs(item, out);
            }
        }
        PatKind::Record { spread, fields } => {
            for field in fields {
                collect_pattern_local_defs(&field.pat, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordPatSpread::Head(pat) | RecordPatSpread::Tail(pat) => {
                        collect_pattern_local_defs(pat, out);
                    }
                }
            }
        }
        PatKind::Con(_, payload) => {
            if let Some(payload) = payload {
                collect_pattern_local_defs(payload, out);
            }
        }
        PatKind::Or(left, right) => {
            collect_pattern_local_defs(left, out);
            collect_pattern_local_defs(right, out);
        }
        PatKind::As(inner, def) => {
            collect_pattern_local_defs(inner, out);
            if !out.contains(def) {
                out.push(*def);
            }
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::UnresolvedName(_) => {}
    }
}

fn role_method_input_tv_map_for_export(
    info: &crate::solve::RoleMethodInfo,
    arg_infos: &[crate::solve::RoleArgInfo],
    recv_tv: Option<TypeVar>,
    arg_tvs: &[TypeVar],
) -> Option<HashMap<String, Vec<TypeVar>>> {
    let mut mapped = HashMap::<String, Vec<TypeVar>>::new();
    let mut remaining_arg_tvs = arg_tvs;
    if info.has_receiver {
        let recv_tv = match recv_tv {
            Some(recv_tv) => recv_tv,
            None => {
                let (recv_tv, rest) = arg_tvs.split_first()?;
                remaining_arg_tvs = rest;
                *recv_tv
            }
        };
        let recv_name = arg_infos.iter().find(|info| info.is_input)?.name.clone();
        mapped.entry(recv_name).or_default().push(recv_tv);
    }
    for (arg_tv, sig_name) in remaining_arg_tvs.iter().zip(&info.input_names) {
        if let Some(name) = sig_name {
            mapped.entry(name.clone()).or_default().push(*arg_tv);
        }
    }
    Some(mapped)
}

fn type_from_bounds(bounds: erased::TypeBounds) -> erased::Type {
    match (bounds.lower, bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => *lower,
        (Some(lower), Some(upper)) if matches!(*lower, erased::Type::Never) => *upper,
        (Some(lower), Some(upper)) if matches!(*upper, erased::Type::Any) => *lower,
        (Some(lower), Some(upper)) => erased::Type::Inter(vec![*lower, *upper]),
        (Some(lower), None) => *lower,
        (None, Some(upper)) => *upper,
        (None, None) => erased::Type::Unknown,
    }
}

fn export_name(name: &Name) -> erased::Name {
    erased::Name(name.0.clone())
}

fn export_path(path: &Path) -> erased::Path {
    erased::Path {
        segments: path.segments.iter().map(export_name).collect(),
    }
}

fn export_def_id(def: DefId) -> erased::DefId {
    erased::DefId(def.0)
}

fn export_ref_id(ref_id: RefId) -> erased::RefId {
    erased::RefId(ref_id.0)
}

fn export_type_var(tv: crate::ids::TypeVar) -> erased::TypeVar {
    erased::TypeVar(format!("t{}", tv.0))
}

fn export_lit(lit: &LowerLit) -> erased::Lit {
    match lit {
        LowerLit::Int(value) => erased::Lit::Int(value.clone()),
        LowerLit::Float(value) => erased::Lit::Float(value.to_string()),
        LowerLit::Str(value) => erased::Lit::String(value.clone()),
        LowerLit::Bool(value) => erased::Lit::Bool(*value),
        LowerLit::Unit => erased::Lit::Unit,
    }
}

fn convert_scheme_with_fallback_quantified(
    scheme: typed_ir::Scheme,
    quantified_types: Vec<erased::TypeVar>,
) -> erased::Scheme {
    if quantified_types.is_empty() {
        let body = convert_type(scheme.body);
        return erased::Scheme {
            quantified_types: collect_type_vars(&body),
            body,
            quantified_effects: Vec::new(),
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: scheme
                .requirements
                .into_iter()
                .map(convert_role_requirement)
                .collect(),
        };
    }
    convert_scheme(scheme, quantified_types)
}

fn convert_scheme(
    scheme: typed_ir::Scheme,
    quantified_types: Vec<erased::TypeVar>,
) -> erased::Scheme {
    erased::Scheme {
        body: convert_type(scheme.body),
        quantified_types,
        quantified_effects: Vec::new(),
        quantified_refs: Vec::new(),
        typeclass_obligations: Vec::new(),
        requirements: scheme
            .requirements
            .into_iter()
            .map(convert_role_requirement)
            .collect(),
    }
}

fn convert_role_requirement(requirement: typed_ir::RoleRequirement) -> erased::RoleRequirement {
    erased::RoleRequirement {
        role: convert_typed_path(requirement.role),
        args: requirement
            .args
            .into_iter()
            .map(|arg| match arg {
                typed_ir::RoleRequirementArg::Input(bounds) => {
                    erased::RoleRequirementArg::Input(convert_type_bounds(bounds))
                }
                typed_ir::RoleRequirementArg::Associated { name, bounds } => {
                    erased::RoleRequirementArg::Associated {
                        name: convert_typed_name(name),
                        bounds: convert_type_bounds(bounds),
                    }
                }
            })
            .collect(),
    }
}

fn convert_type_bounds(bounds: typed_ir::TypeBounds) -> erased::TypeBounds {
    erased::TypeBounds {
        lower: bounds.lower.map(|ty| Box::new(convert_type(*ty))),
        upper: bounds.upper.map(|ty| Box::new(convert_type(*ty))),
    }
}

fn convert_type(ty: typed_ir::Type) -> erased::Type {
    match ty {
        typed_ir::Type::Unknown => erased::Type::Unknown,
        typed_ir::Type::Never => erased::Type::Never,
        typed_ir::Type::Any => erased::Type::Any,
        typed_ir::Type::Var(var) => erased::Type::Var(erased::TypeVar(var.0)),
        typed_ir::Type::Named { path, args } => erased::Type::Named {
            path: convert_typed_path(path),
            args: args.into_iter().map(convert_type_arg).collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => erased::Type::Fun {
            param: Box::new(convert_type(*param)),
            param_effect: Box::new(convert_type(*param_effect)),
            ret_effect: Box::new(convert_type(*ret_effect)),
            ret: Box::new(convert_type(*ret)),
        },
        typed_ir::Type::Tuple(items) => {
            erased::Type::Tuple(items.into_iter().map(convert_type).collect())
        }
        typed_ir::Type::Record(record) => erased::Type::Record(erased::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| erased::RecordField {
                    name: convert_typed_name(field.name),
                    value: convert_type(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    erased::RecordSpread::Head(Box::new(convert_type(*ty)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    erased::RecordSpread::Tail(Box::new(convert_type(*ty)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => erased::Type::Variant(erased::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| erased::VariantCase {
                    name: convert_typed_name(case.name),
                    payloads: case.payloads.into_iter().map(convert_type).collect(),
                })
                .collect(),
            tail: variant.tail.map(|tail| Box::new(convert_type(*tail))),
        }),
        typed_ir::Type::Row { items, tail } => erased::Type::Row {
            items: items.into_iter().map(convert_type).collect(),
            tail: Box::new(convert_type(*tail)),
        },
        typed_ir::Type::Union(items) => {
            erased::Type::Union(items.into_iter().map(convert_type).collect())
        }
        typed_ir::Type::Inter(items) => {
            erased::Type::Inter(items.into_iter().map(convert_type).collect())
        }
        typed_ir::Type::Recursive { var, body } => erased::Type::Recursive {
            var: erased::TypeVar(var.0),
            body: Box::new(convert_type(*body)),
        },
    }
}

fn convert_type_arg(arg: typed_ir::TypeArg) -> erased::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => erased::TypeArg::Type(convert_type(ty)),
        typed_ir::TypeArg::Bounds(bounds) => erased::TypeArg::Bounds(convert_type_bounds(bounds)),
    }
}

fn collect_type_vars(ty: &erased::Type) -> Vec<erased::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars_inner(ty, &mut vars);
    vars.into_iter().collect()
}

fn collect_type_vars_inner(ty: &erased::Type, out: &mut BTreeSet<erased::TypeVar>) {
    match ty {
        erased::Type::Var(var) => {
            out.insert(var.clone());
        }
        erased::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_vars(arg, out);
            }
        }
        erased::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars_inner(param, out);
            collect_type_vars_inner(param_effect, out);
            collect_type_vars_inner(ret_effect, out);
            collect_type_vars_inner(ret, out);
        }
        erased::Type::Tuple(items) | erased::Type::Union(items) | erased::Type::Inter(items) => {
            for item in items {
                collect_type_vars_inner(item, out);
            }
        }
        erased::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars_inner(&field.value, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    erased::RecordSpread::Head(ty) | erased::RecordSpread::Tail(ty) => {
                        collect_type_vars_inner(ty, out);
                    }
                }
            }
        }
        erased::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars_inner(payload, out);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_vars_inner(tail, out);
            }
        }
        erased::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars_inner(item, out);
            }
            collect_type_vars_inner(tail, out);
        }
        erased::Type::Recursive { body, .. } => {
            collect_type_vars_inner(body, out);
        }
        erased::Type::Unknown | erased::Type::Never | erased::Type::Any => {}
    }
}

fn collect_type_arg_vars(arg: &erased::TypeArg, out: &mut BTreeSet<erased::TypeVar>) {
    match arg {
        erased::TypeArg::Type(ty) => collect_type_vars_inner(ty, out),
        erased::TypeArg::Bounds(bounds) => {
            if let Some(lower) = &bounds.lower {
                collect_type_vars_inner(lower, out);
            }
            if let Some(upper) = &bounds.upper {
                collect_type_vars_inner(upper, out);
            }
        }
    }
}

fn convert_typed_name(name: typed_ir::Name) -> erased::Name {
    erased::Name(name.0)
}

fn convert_typed_path(path: typed_ir::Path) -> erased::Path {
    erased::Path {
        segments: path.segments.into_iter().map(convert_typed_name).collect(),
    }
}

fn convert_primitive_op(op: typed_ir::PrimitiveOp) -> erased::PrimitiveOp {
    match op {
        typed_ir::PrimitiveOp::YadaYada => erased::PrimitiveOp::YadaYada,
        typed_ir::PrimitiveOp::BoolNot => erased::PrimitiveOp::BoolNot,
        typed_ir::PrimitiveOp::BoolEq => erased::PrimitiveOp::BoolEq,
        typed_ir::PrimitiveOp::ListEmpty => erased::PrimitiveOp::ListEmpty,
        typed_ir::PrimitiveOp::ListSingleton => erased::PrimitiveOp::ListSingleton,
        typed_ir::PrimitiveOp::ListLen => erased::PrimitiveOp::ListLen,
        typed_ir::PrimitiveOp::ListMerge => erased::PrimitiveOp::ListMerge,
        typed_ir::PrimitiveOp::ListIndex => erased::PrimitiveOp::ListIndex,
        typed_ir::PrimitiveOp::ListIndexRange => erased::PrimitiveOp::ListIndexRange,
        typed_ir::PrimitiveOp::ListSplice => erased::PrimitiveOp::ListSplice,
        typed_ir::PrimitiveOp::ListIndexRangeRaw => erased::PrimitiveOp::ListIndexRangeRaw,
        typed_ir::PrimitiveOp::ListSpliceRaw => erased::PrimitiveOp::ListSpliceRaw,
        typed_ir::PrimitiveOp::ListViewRaw => erased::PrimitiveOp::ListViewRaw,
        typed_ir::PrimitiveOp::StringLen => erased::PrimitiveOp::StringLen,
        typed_ir::PrimitiveOp::StringIndex => erased::PrimitiveOp::StringIndex,
        typed_ir::PrimitiveOp::StringIndexRange => erased::PrimitiveOp::StringIndexRange,
        typed_ir::PrimitiveOp::StringSplice => erased::PrimitiveOp::StringSplice,
        typed_ir::PrimitiveOp::StringIndexRangeRaw => erased::PrimitiveOp::StringIndexRangeRaw,
        typed_ir::PrimitiveOp::StringSpliceRaw => erased::PrimitiveOp::StringSpliceRaw,
        typed_ir::PrimitiveOp::StringLineCount => erased::PrimitiveOp::StringLineCount,
        typed_ir::PrimitiveOp::StringLineRange => erased::PrimitiveOp::StringLineRange,
        typed_ir::PrimitiveOp::IntAdd => erased::PrimitiveOp::IntAdd,
        typed_ir::PrimitiveOp::IntSub => erased::PrimitiveOp::IntSub,
        typed_ir::PrimitiveOp::IntMul => erased::PrimitiveOp::IntMul,
        typed_ir::PrimitiveOp::IntDiv => erased::PrimitiveOp::IntDiv,
        typed_ir::PrimitiveOp::IntMod => erased::PrimitiveOp::IntMod,
        typed_ir::PrimitiveOp::IntEq => erased::PrimitiveOp::IntEq,
        typed_ir::PrimitiveOp::IntLt => erased::PrimitiveOp::IntLt,
        typed_ir::PrimitiveOp::IntLe => erased::PrimitiveOp::IntLe,
        typed_ir::PrimitiveOp::IntGt => erased::PrimitiveOp::IntGt,
        typed_ir::PrimitiveOp::IntGe => erased::PrimitiveOp::IntGe,
        typed_ir::PrimitiveOp::FloatAdd => erased::PrimitiveOp::FloatAdd,
        typed_ir::PrimitiveOp::FloatSub => erased::PrimitiveOp::FloatSub,
        typed_ir::PrimitiveOp::FloatMul => erased::PrimitiveOp::FloatMul,
        typed_ir::PrimitiveOp::FloatDiv => erased::PrimitiveOp::FloatDiv,
        typed_ir::PrimitiveOp::FloatEq => erased::PrimitiveOp::FloatEq,
        typed_ir::PrimitiveOp::FloatLt => erased::PrimitiveOp::FloatLt,
        typed_ir::PrimitiveOp::FloatLe => erased::PrimitiveOp::FloatLe,
        typed_ir::PrimitiveOp::FloatGt => erased::PrimitiveOp::FloatGt,
        typed_ir::PrimitiveOp::FloatGe => erased::PrimitiveOp::FloatGe,
        typed_ir::PrimitiveOp::StringEq => erased::PrimitiveOp::StringEq,
        typed_ir::PrimitiveOp::StringConcat => erased::PrimitiveOp::StringConcat,
        typed_ir::PrimitiveOp::StringToBytes => erased::PrimitiveOp::StringToBytes,
        typed_ir::PrimitiveOp::CharEq => erased::PrimitiveOp::CharEq,
        typed_ir::PrimitiveOp::CharToString => erased::PrimitiveOp::CharToString,
        typed_ir::PrimitiveOp::CharIsWhitespace => erased::PrimitiveOp::CharIsWhitespace,
        typed_ir::PrimitiveOp::CharIsPunctuation => erased::PrimitiveOp::CharIsPunctuation,
        typed_ir::PrimitiveOp::CharIsWord => erased::PrimitiveOp::CharIsWord,
        typed_ir::PrimitiveOp::BytesLen => erased::PrimitiveOp::BytesLen,
        typed_ir::PrimitiveOp::BytesEq => erased::PrimitiveOp::BytesEq,
        typed_ir::PrimitiveOp::BytesConcat => erased::PrimitiveOp::BytesConcat,
        typed_ir::PrimitiveOp::BytesIndex => erased::PrimitiveOp::BytesIndex,
        typed_ir::PrimitiveOp::BytesIndexRange => erased::PrimitiveOp::BytesIndexRange,
        typed_ir::PrimitiveOp::BytesToUtf8Raw => erased::PrimitiveOp::BytesToUtf8Raw,
        typed_ir::PrimitiveOp::BytesToPath => erased::PrimitiveOp::BytesToPath,
        typed_ir::PrimitiveOp::PathToBytes => erased::PrimitiveOp::PathToBytes,
        typed_ir::PrimitiveOp::IntToString => erased::PrimitiveOp::IntToString,
        typed_ir::PrimitiveOp::IntToHex => erased::PrimitiveOp::IntToHex,
        typed_ir::PrimitiveOp::IntToUpperHex => erased::PrimitiveOp::IntToUpperHex,
        typed_ir::PrimitiveOp::FloatToString => erased::PrimitiveOp::FloatToString,
        typed_ir::PrimitiveOp::BoolToString => erased::PrimitiveOp::BoolToString,
    }
}

#[cfg(test)]
mod tests {
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;

    use super::*;
    use crate::lower::stmt::lower_root;

    fn parse_and_lower(src: &str) -> LowerState {
        let green = yulang_parser::parse_module_to_green(src);
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);
        state
    }

    #[test]
    fn erased_export_reintroduces_ref_id_for_global_def_use() {
        let mut state = parse_and_lower("my id x = x\nid 1\n");
        let id_def = state
            .ctx
            .resolve_value(&Name("id".to_string()))
            .expect("id binding");
        let exported = export_erased_program(&mut state).erased;

        let refs = collect_expr_refs(&exported.module.root_exprs[0].ir);
        assert!(
            !refs.is_empty(),
            "root expression should contain RefId holes"
        );
        assert!(
            refs.iter()
                .any(|ref_id| exported.refs.direct.get(ref_id) == Some(&export_def_id(id_def))),
            "global id use should be represented by RefId -> DefId direct table, refs={:?}, table={:?}",
            refs,
            exported.refs.direct,
        );
    }

    #[test]
    fn erased_export_drops_representation_coerce_nodes() {
        let mut state =
            parse_and_lower("struct point { x: int }\nmy p = point { x: 1 }\nmy px = p.x");
        let typed = crate::export_core_program(&mut state);
        assert!(
            format!("{:?}", typed.program).contains("Coerce"),
            "legacy typed export should still expose coerce evidence for this canary",
        );

        let exported = export_erased_program(&mut state).erased;
        assert!(
            !format!("{:?}", exported.module).contains("Coerce"),
            "erased IR must not expose coerce nodes or coerce evidence",
        );
    }

    #[test]
    fn erased_scheme_exports_quantified_type_vars() {
        let mut state = parse_and_lower("my id x = x\n");
        let exported = export_erased_program(&mut state).erased;
        let id = exported
            .module
            .bindings
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "id")
            })
            .expect("id binding");

        assert!(
            !id.scheme.quantified_types.is_empty(),
            "generic erased scheme should expose quantified type vars: {:?}",
            id.scheme,
        );
        assert!(
            id.scheme.quantified_refs.is_empty(),
            "direct generic id has no typeclass ref obligations"
        );
        assert!(
            id.scheme.typeclass_obligations.is_empty(),
            "direct generic id has no typeclass obligations"
        );
    }

    #[test]
    fn erased_export_uses_bind_pattern_for_direct_let() {
        let mut state = parse_and_lower("my id = { my x = 1\nx }\n");
        let exported = export_erased_program(&mut state).erased;
        let id = exported
            .module
            .bindings
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "id")
            })
            .expect("id binding");
        let erased::ErasedExpr::Block(block) = &id.body.ir else {
            panic!("id body should export as a block: {:?}", id.body.ir);
        };
        let Some(erased::ErasedStmt::Let { pattern, .. }) = block.stmts.first() else {
            panic!("block should start with a let statement: {:?}", block.stmts);
        };

        assert!(
            matches!(pattern, erased::Pattern::Bind(_)),
            "direct let binder should keep DefId identity, got {pattern:?}",
        );
    }

    #[test]
    fn erased_export_records_resolved_role_method_ref() {
        let mut state = parse_and_lower(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
impl Index int bool:\n  type value = string\n  our x.index y = \"ok\"\n\n\
my shown: string = 1.index true\n",
        );
        let exported = export_erased_program(&mut state).erased;
        let shown = exported
            .module
            .bindings
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "shown")
            })
            .expect("shown binding");
        let refs = collect_expr_refs(&shown.body.ir);
        let resolved_ref = exported
            .refs
            .resolved_typeclass
            .iter()
            .find(|(ref_id, resolved)| {
                refs.contains(ref_id)
                    && resolved
                        .class
                        .segments
                        .last()
                        .is_some_and(|name| name.0 == "Index")
            })
            .expect("resolved Index method ref");

        assert_ne!(
            resolved_ref.1.member, resolved_ref.1.impl_member,
            "role member and impl member identities should stay distinct when impl supplies a body",
        );
        assert!(
            !exported.refs.direct.contains_key(resolved_ref.0),
            "resolved typeclass ref should not be folded into direct refs",
        );
    }

    #[test]
    fn erased_export_records_unresolved_role_method_obligation() {
        let mut state =
            parse_and_lower("role Display 'a:\n  our a.display: string\n\nmy show x = x.display\n");
        let display_def = state
            .ctx
            .resolve_path_value(&Path {
                segments: vec![Name("Display".to_string()), Name("display".to_string())],
            })
            .expect("Display.display member");
        let exported = export_erased_program(&mut state).erased;
        let show = exported
            .module
            .bindings
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "show")
            })
            .expect("show binding");
        let refs = collect_expr_refs(&show.body.ir);
        let obligation = show
            .scheme
            .typeclass_obligations
            .iter()
            .find(|obligation| {
                refs.contains(&obligation.ref_id)
                    && obligation
                        .class
                        .segments
                        .last()
                        .is_some_and(|name| name.0 == "Display")
            })
            .expect("Display typeclass obligation");

        assert_eq!(obligation.member, export_def_id(display_def));
        assert!(
            show.scheme.quantified_refs.contains(&obligation.ref_id),
            "unresolved typeclass ref should be quantified by the binding scheme",
        );
        assert!(
            !exported.refs.direct.contains_key(&obligation.ref_id)
                && !exported
                    .refs
                    .resolved_typeclass
                    .contains_key(&obligation.ref_id),
            "unresolved typeclass ref should live in scheme obligations, not global ref tables",
        );
    }

    #[test]
    fn erased_export_records_unresolved_role_method_associated_output() {
        let mut state = parse_and_lower(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
my get xs key = xs.index key\n",
        );
        let index_def = state
            .ctx
            .resolve_path_value(&Path {
                segments: vec![Name("Index".to_string()), Name("index".to_string())],
            })
            .expect("Index.index member");
        let exported = export_erased_program(&mut state).erased;
        let get = exported
            .module
            .bindings
            .iter()
            .find(|binding| {
                binding
                    .name
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "get")
            })
            .expect("get binding");
        let obligation = get
            .scheme
            .typeclass_obligations
            .iter()
            .find(|obligation| {
                obligation.member == export_def_id(index_def)
                    && obligation
                        .class
                        .segments
                        .last()
                        .is_some_and(|name| name.0 == "Index")
            })
            .expect("Index typeclass obligation");

        assert_eq!(
            obligation.args.len(),
            2,
            "Index obligation should keep container and key input args",
        );
        assert!(
            obligation
                .associated
                .iter()
                .any(|associated| associated.name.0 == "value"),
            "Index obligation should keep associated output constraint, got {obligation:?}",
        );
    }

    fn collect_expr_refs(expr: &erased::ErasedExpr) -> Vec<erased::RefId> {
        let mut refs = Vec::new();
        visit_expr(expr, &mut |expr| {
            if let erased::ErasedExpr::Ref(ref_id) = expr {
                refs.push(*ref_id);
            }
        });
        refs
    }

    fn visit_expr(expr: &erased::ErasedExpr, visitor: &mut impl FnMut(&erased::ErasedExpr)) {
        visitor(expr);
        match expr {
            erased::ErasedExpr::Apply { callee, arg } => {
                visit_expr(callee, visitor);
                visit_expr(arg, visitor);
            }
            erased::ErasedExpr::RefSet { reference, value } => {
                visit_expr(reference, visitor);
                visit_expr(value, visitor);
            }
            erased::ErasedExpr::Lambda { body, .. }
            | erased::ErasedExpr::BindHere { expr: body }
            | erased::ErasedExpr::Pack { expr: body, .. } => visit_expr(body, visitor),
            erased::ErasedExpr::Tuple(items) => {
                for item in items {
                    visit_expr(item, visitor);
                }
            }
            erased::ErasedExpr::Record { fields, spread } => {
                for field in fields {
                    visit_expr(&field.value, visitor);
                }
                if let Some(spread) = spread {
                    match spread {
                        erased::RecordSpreadExpr::Head(expr)
                        | erased::RecordSpreadExpr::Tail(expr) => visit_expr(expr, visitor),
                    }
                }
            }
            erased::ErasedExpr::Variant { value, .. } => {
                if let Some(value) = value {
                    visit_expr(value, visitor);
                }
            }
            erased::ErasedExpr::Select { base, .. } => visit_expr(base, visitor),
            erased::ErasedExpr::Match { scrutinee, arms } => {
                visit_expr(scrutinee, visitor);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        visit_expr(guard, visitor);
                    }
                    visit_expr(&arm.body, visitor);
                }
            }
            erased::ErasedExpr::Handle { body, arms } => {
                visit_expr(body, visitor);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        visit_expr(guard, visitor);
                    }
                    visit_expr(&arm.body, visitor);
                }
            }
            erased::ErasedExpr::Block(block) => {
                for stmt in &block.stmts {
                    match stmt {
                        erased::ErasedStmt::Let { value, .. } | erased::ErasedStmt::Expr(value) => {
                            visit_expr(value, visitor)
                        }
                        erased::ErasedStmt::Module { body, .. } => visit_block(body, visitor),
                    }
                }
                if let Some(tail) = &block.tail {
                    visit_expr(tail, visitor);
                }
            }
            erased::ErasedExpr::Def(_)
            | erased::ErasedExpr::Ref(_)
            | erased::ErasedExpr::PrimitiveOp(_)
            | erased::ErasedExpr::Lit(_) => {}
        }
    }

    fn visit_block(block: &erased::ErasedBlock, visitor: &mut impl FnMut(&erased::ErasedExpr)) {
        for stmt in &block.stmts {
            match stmt {
                erased::ErasedStmt::Let { value, .. } | erased::ErasedStmt::Expr(value) => {
                    visit_expr(value, visitor)
                }
                erased::ErasedStmt::Module { body, .. } => visit_block(body, visitor),
            }
        }
        if let Some(tail) = &block.tail {
            visit_expr(tail, visitor);
        }
    }
}
