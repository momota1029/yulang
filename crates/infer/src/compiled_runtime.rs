use serde::{Deserialize, Serialize};

use poly::dump::DumpLabels;
use poly::expr::{
    Arena as PolyArena, ArgEffectContract, CaseArm, CastRule, CatchArm, CatchOperation,
    Constructor, Def, DefId, EffectOperation, Expr, ExprId, Pat, PatId, RecordPatField,
    RecordSpread, RefId, RuntimeRoot, SelectId, SelectResolution, Stmt,
};
use poly::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleImplMethod,
};
use rustc_hash::FxHashMap;

use crate::lowering::BodyLowering;
use crate::{CompiledTypeArena, CompiledTypeImporter};

/// Lowered per-unit runtime surface.
///
/// The namespace/typed surfaces are enough for parsing and type lookup, but not
/// for executing cached dependency values. Runtime import needs the lowered
/// poly body graph and the labels that keep diagnostics/dumps readable. The
/// remap/merge step is intentionally separate from this serialized surface.
#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledRuntimeSurface {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
}

pub struct CompiledRuntimeImport {
    pub defs: FxHashMap<DefId, DefId>,
    pub exprs: FxHashMap<ExprId, ExprId>,
    pub pats: FxHashMap<PatId, PatId>,
    pub refs: FxHashMap<RefId, RefId>,
    pub selects: FxHashMap<SelectId, SelectId>,
    pub roots: Vec<DefId>,
    pub runtime_roots: Vec<RuntimeRoot>,
    pub root_exprs: Vec<ExprId>,
}

impl CompiledRuntimeSurface {
    pub fn from_lowering(lowering: &BodyLowering) -> Self {
        Self {
            arena: lowering.session.poly.clone(),
            labels: lowering.labels.clone(),
        }
    }

    pub fn import_into(
        &self,
        target: &mut PolyArena,
        labels: &mut DumpLabels,
    ) -> CompiledRuntimeImport {
        let mut import = CompiledRuntimeImport::new();
        reserve_def_ids(&self.arena, target, &mut import);
        reserve_ref_ids(&self.arena, target, &mut import);
        reserve_select_ids(&self.arena, target, &mut import);
        reserve_expr_ids(&self.arena, target, &mut import);
        reserve_pat_ids(&self.arena, target, &mut import);

        let source_types = CompiledTypeArena::from_type_arena(&self.arena.typ);
        let (defs, cast_rules, role_impls) = {
            let mut type_importer = CompiledTypeImporter::new(&source_types, target);
            (
                import_defs(&self.arena, &import, &mut type_importer),
                import_cast_rules(&self.arena, &import, &mut type_importer),
                import_role_impls(&self.arena, &import, &mut type_importer),
            )
        };

        import_refs(&self.arena, target, &import);
        import_selects(&self.arena, target, &import);
        import_exprs(&self.arena, target, &import);
        import_pats(&self.arena, target, &import);
        for (id, def) in defs {
            target.defs.set(id, def);
        }

        import.roots = self
            .arena
            .roots
            .iter()
            .map(|id| import.map_def(*id))
            .collect();
        import.runtime_roots = self
            .arena
            .runtime_roots
            .iter()
            .map(|root| import_runtime_root(root, &import))
            .collect();
        import.root_exprs = self
            .arena
            .root_exprs
            .iter()
            .map(|id| import.map_expr(*id))
            .collect();
        target.roots.extend(import.roots.iter().copied());
        target
            .runtime_roots
            .extend(import.runtime_roots.iter().copied());
        target.root_exprs.extend(import.root_exprs.iter().copied());

        import_root_expr_defs(&self.arena, target, &import);
        target.cast_rules.extend(cast_rules);
        for candidate in role_impls {
            target.role_impls.insert(candidate);
        }
        import_effect_operations(&self.arena, target, &import);
        import_constructors(&self.arena, target, &import);
        import_arg_effect_contracts(&self.arena, target, &import);
        import_field_projections(&self.arena, target, &import);
        import_labels(&self.labels, labels, &import);
        import
    }
}

impl CompiledRuntimeImport {
    fn new() -> Self {
        Self {
            defs: FxHashMap::default(),
            exprs: FxHashMap::default(),
            pats: FxHashMap::default(),
            refs: FxHashMap::default(),
            selects: FxHashMap::default(),
            roots: Vec::new(),
            runtime_roots: Vec::new(),
            root_exprs: Vec::new(),
        }
    }

    fn map_def(&self, id: DefId) -> DefId {
        *self
            .defs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime def id {} is missing", id.0))
    }

    fn map_expr(&self, id: ExprId) -> ExprId {
        *self
            .exprs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime expr id {} is missing", id.0))
    }

    fn map_pat(&self, id: PatId) -> PatId {
        *self
            .pats
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime pattern id {} is missing", id.0))
    }

    fn map_ref(&self, id: RefId) -> RefId {
        *self
            .refs
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime ref id {} is missing", id.0))
    }

    fn map_select(&self, id: SelectId) -> SelectId {
        *self
            .selects
            .get(&id)
            .unwrap_or_else(|| panic!("compiled runtime select id {} is missing", id.0))
    }
}

fn reserve_def_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for id in sorted_def_ids(source) {
        import.defs.insert(id, target.defs.fresh());
    }
}

fn reserve_ref_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for index in 0..source.refs().len() {
        import.refs.insert(RefId(index as u32), target.add_ref());
    }
}

fn reserve_select_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
) {
    for (index, select) in source.selects().iter().enumerate() {
        import.selects.insert(
            SelectId(index as u32),
            target.add_select(select.name.clone()),
        );
    }
}

fn reserve_expr_ids(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &mut CompiledRuntimeImport,
) {
    for index in 0..source.exprs().len() {
        import
            .exprs
            .insert(ExprId(index as u32), target.reserve_expr_slot());
    }
}

fn reserve_pat_ids(source: &PolyArena, target: &mut PolyArena, import: &mut CompiledRuntimeImport) {
    for index in 0..source.pats().len() {
        import
            .pats
            .insert(PatId(index as u32), target.reserve_pat_slot());
    }
}

fn import_defs(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<(DefId, Def)> {
    sorted_def_ids(source)
        .into_iter()
        .map(|source_id| {
            let target_id = import.map_def(source_id);
            let source_def = source
                .defs
                .get(source_id)
                .unwrap_or_else(|| panic!("compiled runtime def id {} is missing", source_id.0));
            (target_id, import_def(source_def, import, type_importer))
        })
        .collect()
}

fn import_def(
    def: &Def,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Def {
    match def {
        Def::Mod { vis, children } => Def::Mod {
            vis: *vis,
            children: children.iter().map(|id| import.map_def(*id)).collect(),
        },
        Def::Let {
            vis,
            scheme,
            body,
            children,
        } => Def::Let {
            vis: *vis,
            scheme: scheme
                .as_ref()
                .map(|scheme| type_importer.import_scheme(scheme)),
            body: body.map(|id| import.map_expr(id)),
            children: children.iter().map(|id| import.map_def(*id)).collect(),
        },
        Def::Arg => Def::Arg,
    }
}

fn import_refs(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, def) in source.refs().iter().enumerate() {
        let Some(def) = def else {
            continue;
        };
        target.resolve_ref(import.map_ref(RefId(index as u32)), import.map_def(*def));
    }
}

fn import_selects(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, select) in source.selects().iter().enumerate() {
        let Some(resolution) = select.resolution else {
            continue;
        };
        target.resolve_select(
            import.map_select(SelectId(index as u32)),
            import_select_resolution(resolution, import),
        );
    }
}

fn import_exprs(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, expr) in source.exprs().iter().enumerate() {
        let id = import.map_expr(ExprId(index as u32));
        target.set_expr(id, import_expr(expr, import));
    }
}

fn import_pats(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    for (index, pat) in source.pats().iter().enumerate() {
        let id = import.map_pat(PatId(index as u32));
        target.set_pat(id, import_pat(pat, import));
    }
}

fn import_expr(expr: &Expr, import: &CompiledRuntimeImport) -> Expr {
    match expr {
        Expr::Lit(lit) => Expr::Lit(lit.clone()),
        Expr::PrimitiveOp(op) => Expr::PrimitiveOp(*op),
        Expr::Var(id) => Expr::Var(import.map_ref(*id)),
        Expr::App(callee, arg) => Expr::App(import.map_expr(*callee), import.map_expr(*arg)),
        Expr::RefSet(place, value) => {
            Expr::RefSet(import.map_expr(*place), import.map_expr(*value))
        }
        Expr::Lambda(param, body) => Expr::Lambda(import.map_pat(*param), import.map_expr(*body)),
        Expr::Tuple(items) => Expr::Tuple(import_expr_ids(items, import)),
        Expr::Record { fields, spread } => Expr::Record {
            fields: fields
                .iter()
                .map(|(name, expr)| (name.clone(), import.map_expr(*expr)))
                .collect(),
            spread: import_expr_spread(spread, import),
        },
        Expr::PolyVariant(name, payloads) => {
            Expr::PolyVariant(name.clone(), import_expr_ids(payloads, import))
        }
        Expr::Select(receiver, select) => {
            Expr::Select(import.map_expr(*receiver), import.map_select(*select))
        }
        Expr::Case(scrutinee, arms) => Expr::Case(
            import.map_expr(*scrutinee),
            arms.iter()
                .map(|arm| import_case_arm(arm, import))
                .collect(),
        ),
        Expr::Catch(body, arms) => Expr::Catch(
            import.map_expr(*body),
            arms.iter()
                .map(|arm| import_catch_arm(arm, import))
                .collect(),
        ),
        Expr::Block(stmts, result) => Expr::Block(
            stmts.iter().map(|stmt| import_stmt(stmt, import)).collect(),
            result.map(|id| import.map_expr(id)),
        ),
    }
}

fn import_pat(pat: &Pat, import: &CompiledRuntimeImport) -> Pat {
    match pat {
        Pat::Wild => Pat::Wild,
        Pat::Lit(lit) => Pat::Lit(lit.clone()),
        Pat::Tuple(items) => Pat::Tuple(import_pat_ids(items, import)),
        Pat::List {
            prefix,
            spread,
            suffix,
        } => Pat::List {
            prefix: import_pat_ids(prefix, import),
            spread: spread.map(|id| import.map_pat(id)),
            suffix: import_pat_ids(suffix, import),
        },
        Pat::Record { fields, spread } => Pat::Record {
            fields: fields
                .iter()
                .map(|field| RecordPatField {
                    name: field.name.clone(),
                    pat: import.map_pat(field.pat),
                    default: field.default.map(|id| import.map_expr(id)),
                })
                .collect(),
            spread: import_def_spread(spread, import),
        },
        Pat::PolyVariant(name, payloads) => {
            Pat::PolyVariant(name.clone(), import_pat_ids(payloads, import))
        }
        Pat::Con(constructor, payloads) => Pat::Con(
            import.map_ref(*constructor),
            import_pat_ids(payloads, import),
        ),
        Pat::Ref(id) => Pat::Ref(import.map_ref(*id)),
        Pat::Var(id) => Pat::Var(import.map_def(*id)),
        Pat::Or(left, right) => Pat::Or(import.map_pat(*left), import.map_pat(*right)),
        Pat::As(pat, binding) => Pat::As(import.map_pat(*pat), import.map_def(*binding)),
    }
}

fn import_stmt(stmt: &Stmt, import: &CompiledRuntimeImport) -> Stmt {
    match stmt {
        Stmt::Let(vis, pat, expr) => Stmt::Let(*vis, import.map_pat(*pat), import.map_expr(*expr)),
        Stmt::Expr(expr) => Stmt::Expr(import.map_expr(*expr)),
        Stmt::Module(def, stmts) => Stmt::Module(
            import.map_def(*def),
            stmts.iter().map(|stmt| import_stmt(stmt, import)).collect(),
        ),
    }
}

fn import_case_arm(arm: &CaseArm, import: &CompiledRuntimeImport) -> CaseArm {
    CaseArm {
        pat: import.map_pat(arm.pat),
        guard: arm.guard.map(|id| import.map_expr(id)),
        body: import.map_expr(arm.body),
    }
}

fn import_catch_arm(arm: &CatchArm, import: &CompiledRuntimeImport) -> CatchArm {
    CatchArm {
        operation: arm
            .operation
            .as_ref()
            .map(|operation| import_catch_operation(operation, import)),
        pat: import.map_pat(arm.pat),
        continuation: arm.continuation.map(|id| import.map_pat(id)),
        guard: arm.guard.map(|id| import.map_expr(id)),
        body: import.map_expr(arm.body),
    }
}

fn import_catch_operation(
    operation: &CatchOperation,
    import: &CompiledRuntimeImport,
) -> CatchOperation {
    CatchOperation {
        path: operation.path.clone(),
        def: operation.def.map(|id| import.map_def(id)),
    }
}

fn import_select_resolution(
    resolution: SelectResolution,
    import: &CompiledRuntimeImport,
) -> SelectResolution {
    match resolution {
        SelectResolution::RecordField => SelectResolution::RecordField,
        SelectResolution::Method { def } => SelectResolution::Method {
            def: import.map_def(def),
        },
        SelectResolution::TypeclassMethod { member } => SelectResolution::TypeclassMethod {
            member: import.map_def(member),
        },
    }
}

fn import_runtime_root(root: &RuntimeRoot, import: &CompiledRuntimeImport) -> RuntimeRoot {
    match root {
        RuntimeRoot::Expr(id) => RuntimeRoot::Expr(import.map_expr(*id)),
        RuntimeRoot::ComputedDef(id) => RuntimeRoot::ComputedDef(import.map_def(*id)),
    }
}

fn import_root_expr_defs(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut pairs = source.root_expr_defs.iter().collect::<Vec<_>>();
    pairs.sort_by_key(|(expr, _)| expr.0);
    for (expr, def) in pairs {
        target
            .root_expr_defs
            .insert(import.map_expr(*expr), import.map_def(*def));
    }
}

fn import_cast_rules(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<CastRule> {
    source
        .cast_rules
        .iter()
        .map(|rule| CastRule {
            def: import.map_def(rule.def),
            source: rule.source.clone(),
            target: rule.target.clone(),
            scheme: type_importer.import_scheme(&rule.scheme),
        })
        .collect()
}

fn import_role_impls(
    source: &PolyArena,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> Vec<RoleImplCandidate> {
    source
        .role_impls
        .iter()
        .map(|candidate| import_role_impl_candidate(candidate, import, type_importer))
        .collect()
}

fn import_role_impl_candidate(
    candidate: &RoleImplCandidate,
    import: &CompiledRuntimeImport,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleImplCandidate {
    RoleImplCandidate {
        impl_def: candidate.impl_def.map(|id| import.map_def(id)),
        role: candidate.role.clone(),
        inputs: candidate
            .inputs
            .iter()
            .map(|arg| import_role_constraint_arg(arg, type_importer))
            .collect(),
        associated: candidate
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: import_role_constraint_arg(&associated.value, type_importer),
            })
            .collect(),
        prerequisites: candidate
            .prerequisites
            .iter()
            .map(|constraint| import_role_constraint(constraint, type_importer))
            .collect(),
        methods: candidate
            .methods
            .iter()
            .map(|method| RoleImplMethod {
                requirement: import.map_def(method.requirement),
                implementation: import.map_def(method.implementation),
            })
            .collect(),
    }
}

fn import_role_constraint(
    constraint: &RoleConstraint,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleConstraint {
    RoleConstraint {
        role: constraint.role.clone(),
        inputs: constraint
            .inputs
            .iter()
            .map(|arg| import_role_constraint_arg(arg, type_importer))
            .collect(),
        associated: constraint
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: import_role_constraint_arg(&associated.value, type_importer),
            })
            .collect(),
    }
}

fn import_role_constraint_arg(
    arg: &RoleConstraintArg,
    type_importer: &mut CompiledTypeImporter<'_, '_, PolyArena>,
) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: type_importer.import_pos_id(arg.lower),
        upper: type_importer.import_neg_id(arg.upper),
    }
}

fn import_effect_operations(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut operations = source.effect_operations.iter().collect::<Vec<_>>();
    operations.sort_by_key(|(def, _)| def.0);
    for (def, operation) in operations {
        target.effect_operations.insert(
            import.map_def(*def),
            EffectOperation {
                path: operation.path.clone(),
            },
        );
    }
}

fn import_constructors(source: &PolyArena, target: &mut PolyArena, import: &CompiledRuntimeImport) {
    let mut constructors = source.constructors.iter().collect::<Vec<_>>();
    constructors.sort_by_key(|(def, _)| def.0);
    for (def, constructor) in constructors {
        target.constructors.insert(
            import.map_def(*def),
            Constructor {
                owner_path: constructor.owner_path.clone(),
                name: constructor.name.clone(),
                arity: constructor.arity,
            },
        );
    }
}

fn import_arg_effect_contracts(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut contracts = source.arg_effect_contracts.iter().collect::<Vec<_>>();
    contracts.sort_by_key(|(def, _)| def.0);
    for (def, contract) in contracts {
        target
            .arg_effect_contracts
            .insert(import.map_def(*def), import_arg_effect_contract(contract));
    }
}

fn import_arg_effect_contract(contract: &ArgEffectContract) -> ArgEffectContract {
    contract.clone()
}

fn import_field_projections(
    source: &PolyArena,
    target: &mut PolyArena,
    import: &CompiledRuntimeImport,
) {
    let mut projections = source.field_projections.iter().copied().collect::<Vec<_>>();
    projections.sort_by_key(|def| def.0);
    for def in projections {
        target.field_projections.insert(import.map_def(def));
    }
}

fn import_labels(source: &DumpLabels, target: &mut DumpLabels, import: &CompiledRuntimeImport) {
    let mut def_labels = source.def_labels().collect::<Vec<_>>();
    def_labels.sort_by_key(|(def, _)| def.0);
    for (def, label) in def_labels {
        target.set_def_label(import.map_def(def), label);
    }

    let mut ref_labels = source.ref_labels().collect::<Vec<_>>();
    ref_labels.sort_by_key(|(reference, _)| reference.0);
    for (reference, label) in ref_labels {
        target.set_ref_label(import.map_ref(reference), label);
    }
}

fn import_expr_ids(ids: &[ExprId], import: &CompiledRuntimeImport) -> Vec<ExprId> {
    ids.iter().map(|id| import.map_expr(*id)).collect()
}

fn import_pat_ids(ids: &[PatId], import: &CompiledRuntimeImport) -> Vec<PatId> {
    ids.iter().map(|id| import.map_pat(*id)).collect()
}

fn import_expr_spread(
    spread: &RecordSpread<ExprId>,
    import: &CompiledRuntimeImport,
) -> RecordSpread<ExprId> {
    match spread {
        RecordSpread::Head(id) => RecordSpread::Head(import.map_expr(*id)),
        RecordSpread::Tail(id) => RecordSpread::Tail(import.map_expr(*id)),
        RecordSpread::None => RecordSpread::None,
    }
}

fn import_def_spread(
    spread: &RecordSpread<DefId>,
    import: &CompiledRuntimeImport,
) -> RecordSpread<DefId> {
    match spread {
        RecordSpread::Head(id) => RecordSpread::Head(import.map_def(*id)),
        RecordSpread::Tail(id) => RecordSpread::Tail(import.map_def(*id)),
        RecordSpread::None => RecordSpread::None,
    }
}

fn sorted_def_ids(arena: &PolyArena) -> Vec<DefId> {
    let mut ids = arena.defs.iter().map(|(id, _)| id).collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids
}

#[cfg(test)]
mod tests {
    use sources::{Name, Path, SourceFile};

    use crate::lowering::lower_loaded_files;

    use super::*;

    #[test]
    fn runtime_surface_import_remaps_lowered_arena_ids() {
        let loaded = sources::load(vec![
            source(&[], "mod ops;\npub use ops::*\n"),
            source(
                &["ops"],
                "pub act signal:\n  pub ping: () -> int\n\npub struct Box { value: int }\npub id x = x\npub make = Box { value: 1 }\n",
            ),
        ]);
        let lowering = lower_loaded_files(&loaded).unwrap();
        assert!(lowering.session.poly.effect_operations.len() > 0);
        assert!(lowering.session.poly.constructors.len() > 0);

        let runtime = CompiledRuntimeSurface::from_lowering(&lowering);
        let mut target = PolyArena::new();
        let prefix_def = target.defs.fresh();
        target.defs.set(prefix_def, Def::Arg);
        let mut labels = DumpLabels::new();

        let import = runtime.import_into(&mut target, &mut labels);

        assert_eq!(import.defs.len(), runtime.arena.defs.len());
        assert_eq!(import.exprs.len(), runtime.arena.exprs().len());
        assert_eq!(import.pats.len(), runtime.arena.pats().len());
        assert_eq!(import.refs.len(), runtime.arena.refs().len());
        assert_eq!(import.selects.len(), runtime.arena.selects().len());
        assert_eq!(import.roots.len(), runtime.arena.roots.len());
        assert_eq!(
            import.runtime_roots.len(),
            runtime.arena.runtime_roots.len()
        );
        assert_eq!(import.root_exprs.len(), runtime.arena.root_exprs.len());
        assert_eq!(
            target.effect_operations.len(),
            runtime.arena.effect_operations.len()
        );
        assert_eq!(target.constructors.len(), runtime.arena.constructors.len());
        assert!(import.defs.iter().any(|(source, target)| source != target));
        assert!(target.defs.get(prefix_def).is_some());

        for root in &import.roots {
            assert!(target.defs.get(*root).is_some());
        }
        for root in &import.runtime_roots {
            match root {
                RuntimeRoot::Expr(expr) => {
                    target.expr(*expr);
                }
                RuntimeRoot::ComputedDef(def) => {
                    assert!(target.defs.get(*def).is_some());
                }
            }
        }
    }

    fn source(module: &[&str], text: &str) -> SourceFile {
        SourceFile {
            module_path: Path {
                segments: module
                    .iter()
                    .map(|segment| Name((*segment).to_string()))
                    .collect(),
            },
            source: text.to_string(),
        }
    }
}
