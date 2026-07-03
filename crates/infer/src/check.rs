//! 推論結果を dump せず、型付けの進み具合と診断の所在だけを集計する入口。
//!
//! `dump` は巨大な文字列表現を作るため、推論そのものの時間や未型付け箇所を切り分けにくい。
//! この module は既存の lowering / inference を一度だけ走らせ、その結果を構造化された summary にする。

use poly::expr::{Def, DefId};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RolePredicateArg, Scheme, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};
use sources::{LoadedFile, Path};

use crate::LoadedFilesError;
use crate::ModuleId;
use crate::constraints::TypeLevel;
use crate::lowering::{BodyLowering, BodyLoweringError, BodyLoweringTiming, lower_loaded_files};
use crate::time::{Duration, Instant};

pub struct PolyCheckOutput {
    pub report: PolyCheckReport,
    pub lowering: BodyLowering,
    pub timing: PolyCheckTiming,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyCheckTiming {
    pub infer: Duration,
    pub summarize: Duration,
    pub lowering: BodyLoweringTiming,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyCheckReport {
    pub totals: CheckTotals,
    pub modules: Vec<ModuleCheck>,
    pub missing_schemes: Vec<CheckedDef>,
    pub bodyless_decls: Vec<CheckedDef>,
    pub diagnostics: Vec<CheckDiagnostic>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CheckTotals {
    pub modules: usize,
    pub module_values: usize,
    pub type_decls: usize,
    pub child_modules: usize,
    pub let_defs: usize,
    pub typed_lets: usize,
    pub missing_schemes: usize,
    pub bodyless_decls: usize,
    pub stack_schemes: usize,
    pub lowering_errors: usize,
    pub unowned_errors: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleCheck {
    pub path: Path,
    pub value_count: usize,
    pub type_count: usize,
    pub child_module_count: usize,
    pub typed_lets: usize,
    pub missing_schemes: usize,
    pub bodyless_decls: usize,
    pub stack_schemes: usize,
    pub local_errors: usize,
    pub missing_scheme_defs: Vec<CheckedDef>,
    pub bodyless_defs: Vec<CheckedDef>,
    pub diagnostics: Vec<CheckDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDef {
    pub def: DefId,
    pub label: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckDiagnostic {
    pub error_index: usize,
    pub def: Option<DefId>,
    pub label: Option<String>,
}

pub fn check_loaded_files(files: &[LoadedFile]) -> Result<PolyCheckOutput, LoadedFilesError> {
    let infer_start = Instant::now();
    let lowering = lower_loaded_files(files)?;
    let infer = infer_start.elapsed();
    let lowering_timing = lowering.timing;

    let summarize_start = Instant::now();
    let report = summarize_lowering(&lowering);
    let summarize = summarize_start.elapsed();

    Ok(PolyCheckOutput {
        report,
        lowering,
        timing: PolyCheckTiming {
            infer,
            summarize,
            lowering: lowering_timing,
        },
    })
}

pub fn summarize_lowering(lowering: &BodyLowering) -> PolyCheckReport {
    let mut report = PolyCheckReport {
        totals: CheckTotals::default(),
        modules: Vec::new(),
        missing_schemes: Vec::new(),
        bodyless_decls: Vec::new(),
        diagnostics: diagnostics(lowering),
    };
    report.totals.lowering_errors = lowering.errors.len();
    report.totals.unowned_errors = report
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.def.is_none())
        .count();

    collect_let_def_totals(lowering, &mut report);

    let diagnostics_by_def = diagnostics_by_def(&report.diagnostics);
    collect_module_checks(
        lowering,
        lowering.modules.root_id(),
        &diagnostics_by_def,
        &mut report,
    );
    report.totals.modules = report.modules.len();

    report
}

pub fn format_inferred_value_type(lowering: &BodyLowering, value: TypeVar) -> String {
    format_inferred_value_type_with_path_rewriter(lowering, value, &|path| path.to_vec())
}

pub fn format_inferred_value_type_with_path_rewriter(
    lowering: &BodyLowering,
    value: TypeVar,
    path_rewriter: &dyn Fn(&[String]) -> Vec<String>,
) -> String {
    let machine = lowering.session.infer.constraints();
    let generalized = crate::generalize::generalize_type_var_with_boundaries(
        machine,
        value,
        TypeLevel::root(),
        TypeLevel::root().child(),
        &FxHashSet::default(),
    );
    let mut types = lowering.session.poly.typ.clone();
    let finalized =
        crate::generalize::finalize_generalized_compact_root(&mut types, machine, &generalized);
    poly::dump::format_scheme_with_path_rewriter(&types, &finalized.scheme, path_rewriter)
}

pub fn format_inferred_value_type_public_with_path_rewriter(
    lowering: &BodyLowering,
    value: TypeVar,
    path_rewriter: &dyn Fn(&[String]) -> Vec<String>,
) -> poly::dump::PublicTypeDisplay {
    let machine = lowering.session.infer.constraints();
    let generalized = crate::generalize::generalize_type_var_with_boundaries(
        machine,
        value,
        TypeLevel::root(),
        TypeLevel::root().child(),
        &FxHashSet::default(),
    );
    let mut types = lowering.session.poly.typ.clone();
    let finalized =
        crate::generalize::finalize_generalized_compact_root(&mut types, machine, &generalized);
    poly::dump::format_scheme_public_with_path_rewriter(&types, &finalized.scheme, path_rewriter)
}

pub fn format_inferred_input_type_with_path_rewriter(
    lowering: &BodyLowering,
    value: TypeVar,
    path_rewriter: &dyn Fn(&[String]) -> Vec<String>,
) -> String {
    let machine = lowering.session.infer.constraints();
    let compact = crate::compact::compact_negative_type_var_for_scheme(machine, value);
    let mut types = lowering.session.poly.typ.clone();
    let ty = crate::compact::finalize_compact_type_to_neg(&mut types, &compact.root);
    poly::dump::format_neg_with_path_rewriter(&types, ty, path_rewriter)
}

pub fn format_inferred_input_type_public_with_path_rewriter(
    lowering: &BodyLowering,
    value: TypeVar,
    path_rewriter: &dyn Fn(&[String]) -> Vec<String>,
) -> poly::dump::PublicTypeDisplay {
    let machine = lowering.session.infer.constraints();
    let compact = crate::compact::compact_negative_type_var_for_scheme(machine, value);
    let mut types = lowering.session.poly.typ.clone();
    let ty = crate::compact::finalize_compact_type_to_neg(&mut types, &compact.root);
    poly::dump::format_neg_public_with_path_rewriter(&types, ty, path_rewriter)
}

pub fn body_error_def(error: &BodyLoweringError) -> Option<DefId> {
    match error {
        BodyLoweringError::MissingBindingDecl { .. }
        | BodyLoweringError::MissingModuleDecl { .. }
        | BodyLoweringError::RootExpr { .. } => None,
        BodyLoweringError::MissingBody { def, .. }
        | BodyLoweringError::NonLetDef { def, .. }
        | BodyLoweringError::Expr { def, .. } => Some(*def),
        BodyLoweringError::Analysis(error) => error.primary_def(),
    }
}

pub fn format_path(path: &Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn collect_let_def_totals(lowering: &BodyLowering, report: &mut PolyCheckReport) {
    for (def, item) in lowering.session.poly.defs.iter() {
        let Def::Let { scheme, body, .. } = item else {
            continue;
        };
        report.totals.let_defs += 1;

        if let Some(scheme) = scheme {
            report.totals.typed_lets += 1;
            if scheme_has_stack(&lowering.session.poly.typ, scheme) {
                report.totals.stack_schemes += 1;
            }
        } else {
            report.totals.missing_schemes += 1;
            report.missing_schemes.push(checked_def(lowering, def));
        }

        if body.is_none() {
            report.totals.bodyless_decls += 1;
            report.bodyless_decls.push(checked_def(lowering, def));
        }
    }
    sort_checked_defs(&mut report.missing_schemes);
    sort_checked_defs(&mut report.bodyless_decls);
}

fn collect_module_checks(
    lowering: &BodyLowering,
    module: ModuleId,
    diagnostics_by_def: &FxHashMap<DefId, Vec<CheckDiagnostic>>,
    report: &mut PolyCheckReport,
) {
    let values = lowering.modules.module_value_decls(module);
    let types = lowering.modules.module_type_decls(module);
    let children = lowering.modules.module_child_decls(module);

    let mut check = ModuleCheck {
        path: lowering.modules.module_path(module),
        value_count: values.len(),
        type_count: types.len(),
        child_module_count: children.len(),
        typed_lets: 0,
        missing_schemes: 0,
        bodyless_decls: 0,
        stack_schemes: 0,
        local_errors: 0,
        missing_scheme_defs: Vec::new(),
        bodyless_defs: Vec::new(),
        diagnostics: Vec::new(),
    };

    for value in values {
        inspect_module_value(lowering, value.def, diagnostics_by_def, &mut check);
    }
    sort_checked_defs(&mut check.missing_scheme_defs);
    sort_checked_defs(&mut check.bodyless_defs);

    report.totals.module_values += check.value_count;
    report.totals.type_decls += check.type_count;
    report.totals.child_modules += check.child_module_count;
    report.modules.push(check);

    for child in children {
        collect_module_checks(lowering, child.module, diagnostics_by_def, report);
    }
}

fn inspect_module_value(
    lowering: &BodyLowering,
    def: DefId,
    diagnostics_by_def: &FxHashMap<DefId, Vec<CheckDiagnostic>>,
    check: &mut ModuleCheck,
) {
    if let Some(diagnostics) = diagnostics_by_def.get(&def) {
        check.local_errors += diagnostics.len();
        check.diagnostics.extend(diagnostics.iter().cloned());
    }
    match lowering.session.poly.defs.get(def) {
        Some(Def::Let { scheme, body, .. }) => {
            if let Some(scheme) = scheme {
                check.typed_lets += 1;
                if scheme_has_stack(&lowering.session.poly.typ, scheme) {
                    check.stack_schemes += 1;
                }
            } else {
                check.missing_schemes += 1;
                check.missing_scheme_defs.push(checked_def(lowering, def));
            }
            if body.is_none() {
                check.bodyless_decls += 1;
                check.bodyless_defs.push(checked_def(lowering, def));
            }
        }
        Some(Def::Mod { .. }) | Some(Def::Arg) | None => {
            check.missing_schemes += 1;
            check.bodyless_decls += 1;
            check.missing_scheme_defs.push(checked_def(lowering, def));
            check.bodyless_defs.push(checked_def(lowering, def));
        }
    }
}

fn diagnostics(lowering: &BodyLowering) -> Vec<CheckDiagnostic> {
    lowering
        .errors
        .iter()
        .enumerate()
        .map(|(error_index, error)| {
            let def = body_error_def(error);
            CheckDiagnostic {
                error_index,
                def,
                label: def.map(|def| def_label(lowering, def)),
            }
        })
        .collect()
}

fn diagnostics_by_def(diagnostics: &[CheckDiagnostic]) -> FxHashMap<DefId, Vec<CheckDiagnostic>> {
    let mut by_def = FxHashMap::default();
    for diagnostic in diagnostics {
        if let Some(def) = diagnostic.def {
            by_def
                .entry(def)
                .or_insert_with(Vec::new)
                .push(diagnostic.clone());
        }
    }
    by_def
}

fn checked_def(lowering: &BodyLowering, def: DefId) -> CheckedDef {
    CheckedDef {
        def,
        label: def_label(lowering, def),
    }
}

fn def_label(lowering: &BodyLowering, def: DefId) -> String {
    lowering
        .labels
        .def_label(def)
        .map(str::to_string)
        .unwrap_or_else(|| format!("d{}", def.0))
}

fn sort_checked_defs(defs: &mut [CheckedDef]) {
    defs.sort_by_key(|item| item.def.0);
}

fn scheme_has_stack(arena: &TypeArena, scheme: &Scheme) -> bool {
    if !scheme.stack_quantifiers.is_empty() {
        return true;
    }
    let mut scan = StackScan::default();
    if scan.pos(arena, scheme.predicate) {
        return true;
    }
    for predicate in &scheme.role_predicates {
        for input in &predicate.inputs {
            if scan.role_arg(arena, *input) {
                return true;
            }
        }
        for associated in &predicate.associated {
            if scan.neu(arena, associated.value) {
                return true;
            }
        }
    }
    for bound in &scheme.recursive_bounds {
        if scan.neu(arena, bound.bounds) {
            return true;
        }
    }
    false
}

#[derive(Default)]
struct StackScan {
    pos: FxHashSet<PosId>,
    neg: FxHashSet<NegId>,
    neu: FxHashSet<NeuId>,
}

impl StackScan {
    fn role_arg(&mut self, arena: &TypeArena, arg: RolePredicateArg) -> bool {
        match arg {
            RolePredicateArg::Covariant(pos) => self.pos(arena, pos),
            RolePredicateArg::Contravariant(neg) => self.neg(arena, neg),
            RolePredicateArg::Invariant(neu) => self.neu(arena, neu),
        }
    }

    fn pos(&mut self, arena: &TypeArena, id: PosId) -> bool {
        if !self.pos.insert(id) {
            return false;
        }
        match arena.pos(id) {
            Pos::Bot | Pos::Var(_) => false,
            Pos::Con(_, args) => self.neu_items(arena, args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neg(arena, *arg)
                    || self.neg(arena, *arg_eff)
                    || self.pos(arena, *ret_eff)
                    || self.pos(arena, *ret)
            }
            Pos::Record(fields) => fields.iter().any(|field| self.pos(arena, field.value)),
            Pos::RecordTailSpread { fields, tail } => {
                fields.iter().any(|field| self.pos(arena, field.value)) || self.pos(arena, *tail)
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.pos(arena, *tail) || fields.iter().any(|field| self.pos(arena, field.value))
            }
            Pos::PolyVariant(variants) => variants
                .iter()
                .any(|(_, payloads)| payloads.iter().any(|payload| self.pos(arena, *payload))),
            Pos::Tuple(items) | Pos::Row(items) => items.iter().any(|item| self.pos(arena, *item)),
            Pos::Stack { .. } | Pos::NonSubtract(_, _) => true,
            Pos::Union(lhs, rhs) => self.pos(arena, *lhs) || self.pos(arena, *rhs),
        }
    }

    fn neg(&mut self, arena: &TypeArena, id: NegId) -> bool {
        if !self.neg.insert(id) {
            return false;
        }
        match arena.neg(id) {
            Neg::Top | Neg::Bot | Neg::Var(_) => false,
            Neg::Con(_, args) => self.neu_items(arena, args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.pos(arena, *arg)
                    || self.pos(arena, *arg_eff)
                    || self.neg(arena, *ret_eff)
                    || self.neg(arena, *ret)
            }
            Neg::Record(fields) => fields.iter().any(|field| self.neg(arena, field.value)),
            Neg::PolyVariant(variants) => variants
                .iter()
                .any(|(_, payloads)| payloads.iter().any(|payload| self.neg(arena, *payload))),
            Neg::Tuple(items) => items.iter().any(|item| self.neg(arena, *item)),
            Neg::Row(items, tail) => {
                items.iter().any(|item| self.neg(arena, *item)) || self.neg(arena, *tail)
            }
            Neg::Stack { .. } => true,
            Neg::Intersection(lhs, rhs) => self.neg(arena, *lhs) || self.neg(arena, *rhs),
        }
    }

    fn neu(&mut self, arena: &TypeArena, id: NeuId) -> bool {
        if !self.neu.insert(id) {
            return false;
        }
        match arena.neu(id) {
            Neu::Bounds(lower, upper) => self.pos(arena, *lower) || self.neg(arena, *upper),
            Neu::Con(_, args) => self.neu_items(arena, args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neu(arena, *arg)
                    || self.neu(arena, *arg_eff)
                    || self.neu(arena, *ret_eff)
                    || self.neu(arena, *ret)
            }
            Neu::Record(fields) => fields.iter().any(|field| self.neu(arena, field.value)),
            Neu::PolyVariant(variants) => variants
                .iter()
                .any(|(_, payloads)| payloads.iter().any(|payload| self.neu(arena, *payload))),
            Neu::Tuple(items) => self.neu_items(arena, items),
        }
    }

    fn neu_items(&mut self, arena: &TypeArena, items: &[NeuId]) -> bool {
        items.iter().any(|item| self.neu(arena, *item))
    }
}
