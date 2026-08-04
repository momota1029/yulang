//! Detached runtime/body graph for typed nominal act templates.
//!
//! M1-3 keeps this graph shadow-only. External targets are deliberately unresolved in the
//! detached `PolyArena` and live in stable-key side tables instead.

#![allow(dead_code, reason = "M1-3 is shadow-only until M1-4 consumes it")]

use super::ModuleTable;
use super::nominal_act_identity::{NominalActInstanceSubstitution, NominalActTemplateIdentity};
use super::typed_act_template::{
    NominalActMemberKey, NominalTypeGraphCloner, StableExternalReferenceKey, TypedActTemplate,
    member_key, path_names,
};
use crate::DefId;
use poly::dump::DumpLabels;
use poly::expr::{
    Arena as PolyArena, CaseArm, CatchArm, CatchOperation, Def, Expr, ExprId, NominalRecordField,
    NominalRecordShape, Pat, PatId, RecordPatField, RecordSpread, RefId, SelectId,
    SelectResolution, Stmt,
};
use rustc_hash::{FxHashMap, FxHashSet};

pub(crate) struct TypedActBodyTemplate {
    pub(crate) arena: PolyArena,
    pub(crate) labels: DumpLabels,
    pub(crate) members: Vec<TypedActBodyMember>,
    pub(crate) external_refs: FxHashMap<RefId, StableExternalReferenceKey>,
    pub(crate) external_selects: FxHashMap<SelectId, StableExternalReferenceKey>,
    pub(crate) external_catches: FxHashMap<CatchSite, StableExternalReferenceKey>,
}

pub(crate) struct TypedActBodyMember {
    pub(crate) key: NominalActMemberKey,
    pub(crate) source: DefId,
    pub(crate) detached: DefId,
}

pub(crate) struct TypedActBodyInstantiation {
    pub(crate) arena: PolyArena,
    pub(crate) labels: DumpLabels,
    pub(crate) member_destinations: FxHashMap<DefId, DefId>,
    pub(crate) external_refs: FxHashMap<RefId, StableExternalReferenceKey>,
    pub(crate) external_selects: FxHashMap<SelectId, StableExternalReferenceKey>,
    pub(crate) external_catches: FxHashMap<CatchSite, StableExternalReferenceKey>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TypedActBodyCensus {
    pub(crate) defs: usize,
    pub(crate) exprs: usize,
    pub(crate) pats: usize,
    pub(crate) refs: usize,
    pub(crate) selects: usize,
    pub(crate) external_refs: usize,
    pub(crate) external_selects: usize,
    pub(crate) external_catches: usize,
    pub(crate) effect_operations: usize,
    pub(crate) constructors: usize,
    pub(crate) nominal_record_shapes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CatchSite {
    pub(crate) expr: ExprId,
    pub(crate) arm: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypedActBodyError {
    MissingDefinition(DefId),
    MissingExternalKey(DefId),
    MissingExternalOperationPath(Vec<String>),
    MissingReferenceTarget(RefId),
    MissingSelectionTarget(SelectId),
    MissingMemberDestination(DefId),
    MissingMemberKey(DefId),
}

impl TypedActTemplate {
    pub(crate) fn capture_body(
        &self,
        identity: &NominalActTemplateIdentity,
        source: &PolyArena,
        modules: &ModuleTable,
        labels: &DumpLabels,
    ) -> Result<TypedActBodyTemplate, TypedActBodyError> {
        let mut internal_defs = internal_def_closure(identity, source)?;
        let selection = BodySelection::from_members(identity, source, &mut internal_defs)?;
        let paths = identity
            .nominal_types
            .iter()
            .map(|nominal| {
                let path = path_names(&nominal.source_path);
                (path.clone(), path)
            })
            .collect::<FxHashMap<_, _>>();
        let root_path = identity
            .nominal_types
            .iter()
            .find(|nominal| nominal.source == identity.root_act)
            .map(|nominal| path_names(&nominal.source_path))
            .ok_or(TypedActBodyError::MissingMemberKey(
                identity.value_members[0].source,
            ))?;
        let mut importer = BodyImporter::new(source, &selection, &paths);
        importer.reserve();
        importer.capture_external_targets(modules, &internal_defs)?;
        importer.import_nodes()?;
        importer.import_runtime_metadata();
        importer.import_labels(labels);
        let members = identity
            .value_members
            .iter()
            .map(|member| {
                Ok(TypedActBodyMember {
                    key: member_key(identity, member, &root_path)
                        .map_err(|_| TypedActBodyError::MissingMemberKey(member.source))?,
                    source: member.source,
                    detached: importer.ids.def(member.source),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        importer.target.roots = members.iter().map(|member| member.detached).collect();
        Ok(TypedActBodyTemplate {
            arena: importer.target,
            labels: importer.labels,
            members,
            external_refs: importer.external_refs,
            external_selects: importer.external_selects,
            external_catches: importer.external_catches,
        })
    }
}

impl TypedActBodyTemplate {
    pub(crate) fn census(&self) -> TypedActBodyCensus {
        body_census(
            &self.arena,
            &self.external_refs,
            &self.external_selects,
            &self.external_catches,
        )
    }

    pub(crate) fn apply(
        &self,
        substitution: &NominalActInstanceSubstitution,
    ) -> Result<TypedActBodyInstantiation, TypedActBodyError> {
        let selection = BodySelection::whole_detached(&self.arena);
        let mut paths = substitution
            .type_path_map
            .iter()
            .map(|(source, destination)| (path_names(source), path_names(destination)))
            .collect::<FxHashMap<_, _>>();
        paths.extend(
            substitution
                .operation_path_map
                .iter()
                .map(|(source, destination)| (path_names(source), path_names(destination))),
        );
        let mut importer = BodyImporter::new(&self.arena, &selection, &paths);
        importer.reserve();
        for (reference, key) in &self.external_refs {
            importer
                .external_refs
                .insert(importer.ids.reference(*reference), key.clone());
        }
        for (select, key) in &self.external_selects {
            importer
                .external_selects
                .insert(importer.ids.select(*select), key.clone());
        }
        for (site, key) in &self.external_catches {
            importer.external_catches.insert(
                CatchSite {
                    expr: importer.ids.expr(site.expr),
                    arm: site.arm,
                },
                key.clone(),
            );
        }
        importer.import_nodes()?;
        importer.import_runtime_metadata();
        importer.import_labels(&self.labels);
        let member_destinations = self
            .members
            .iter()
            .map(|member| {
                let destination = substitution
                    .def_map
                    .get(&member.source)
                    .copied()
                    .ok_or(TypedActBodyError::MissingMemberDestination(member.source))?;
                Ok((importer.ids.def(member.detached), destination))
            })
            .collect::<Result<FxHashMap<_, _>, _>>()?;
        importer.target.roots = member_destinations.keys().copied().collect();
        Ok(TypedActBodyInstantiation {
            arena: importer.target,
            labels: importer.labels,
            member_destinations,
            external_refs: importer.external_refs,
            external_selects: importer.external_selects,
            external_catches: importer.external_catches,
        })
    }
}

impl TypedActBodyInstantiation {
    pub(crate) fn census(&self) -> TypedActBodyCensus {
        body_census(
            &self.arena,
            &self.external_refs,
            &self.external_selects,
            &self.external_catches,
        )
    }
}

fn body_census(
    arena: &PolyArena,
    external_refs: &FxHashMap<RefId, StableExternalReferenceKey>,
    external_selects: &FxHashMap<SelectId, StableExternalReferenceKey>,
    external_catches: &FxHashMap<CatchSite, StableExternalReferenceKey>,
) -> TypedActBodyCensus {
    TypedActBodyCensus {
        defs: arena.defs.len(),
        exprs: arena.exprs().len(),
        pats: arena.pats().len(),
        refs: arena.refs().len(),
        selects: arena.selects().len(),
        external_refs: external_refs.len(),
        external_selects: external_selects.len(),
        external_catches: external_catches.len(),
        effect_operations: arena.effect_operations.len(),
        constructors: arena.constructors.len(),
        nominal_record_shapes: arena.nominal_record_shapes.len(),
    }
}

fn internal_def_closure(
    identity: &NominalActTemplateIdentity,
    source: &PolyArena,
) -> Result<FxHashSet<DefId>, TypedActBodyError> {
    let mut out = FxHashSet::default();
    let mut pending = identity
        .value_members
        .iter()
        .map(|member| member.source)
        .collect::<Vec<_>>();
    while let Some(def) = pending.pop() {
        if !out.insert(def) {
            continue;
        }
        let item = source
            .defs
            .get(def)
            .ok_or(TypedActBodyError::MissingDefinition(def))?;
        let children = match item {
            Def::Mod { children, .. } | Def::Let { children, .. } => children,
            Def::Arg => continue,
        };
        pending.extend(children.iter().copied());
    }
    Ok(out)
}

#[derive(Default)]
struct BodySelection {
    defs: FxHashSet<DefId>,
    exprs: FxHashSet<ExprId>,
    pats: FxHashSet<PatId>,
    refs: FxHashSet<RefId>,
    selects: FxHashSet<SelectId>,
}

impl BodySelection {
    fn from_members(
        identity: &NominalActTemplateIdentity,
        source: &PolyArena,
        internal: &mut FxHashSet<DefId>,
    ) -> Result<Self, TypedActBodyError> {
        let mut out = Self::default();
        for member in &identity.value_members {
            out.select_def(source, internal, member.source)?;
        }
        Ok(out)
    }

    fn whole_detached(source: &PolyArena) -> Self {
        Self {
            defs: source.defs.iter().map(|(id, _)| id).collect(),
            exprs: (0..source.exprs().len())
                .map(|index| ExprId(index as u32))
                .collect(),
            pats: (0..source.pats().len())
                .map(|index| PatId(index as u32))
                .collect(),
            refs: (0..source.refs().len())
                .map(|index| RefId(index as u32))
                .collect(),
            selects: (0..source.selects().len())
                .map(|index| SelectId(index as u32))
                .collect(),
        }
    }

    fn select_def(
        &mut self,
        source: &PolyArena,
        internal: &mut FxHashSet<DefId>,
        def: DefId,
    ) -> Result<(), TypedActBodyError> {
        if !internal.contains(&def) || !self.defs.insert(def) {
            return Ok(());
        }
        match source
            .defs
            .get(def)
            .ok_or(TypedActBodyError::MissingDefinition(def))?
        {
            Def::Mod { children, .. } => {
                for child in children {
                    self.select_def(source, internal, *child)?;
                }
            }
            Def::Let { body, children, .. } => {
                if let Some(body) = body {
                    self.select_expr(source, internal, *body)?;
                }
                for child in children {
                    self.select_def(source, internal, *child)?;
                }
            }
            Def::Arg => {}
        }
        Ok(())
    }

    fn select_ref(&mut self, source: &PolyArena, reference: RefId) {
        self.refs.insert(reference);
        let _ = source;
    }

    fn select_select(&mut self, select: SelectId) {
        self.selects.insert(select);
    }

    fn select_expr(
        &mut self,
        source: &PolyArena,
        internal: &mut FxHashSet<DefId>,
        expr: ExprId,
    ) -> Result<(), TypedActBodyError> {
        if !self.exprs.insert(expr) {
            return Ok(());
        }
        match source.expr(expr) {
            Expr::Lit(_) | Expr::PrimitiveOp(_) => {}
            Expr::Var(reference) => self.select_ref(source, *reference),
            Expr::App(left, right) | Expr::RefSet(left, right) => {
                self.select_expr(source, internal, *left)?;
                self.select_expr(source, internal, *right)?;
            }
            Expr::Lambda(pat, body) => {
                self.select_pat(source, internal, *pat)?;
                self.select_expr(source, internal, *body)?;
            }
            Expr::Tuple(items) | Expr::PolyVariant(_, items) => {
                for item in items {
                    self.select_expr(source, internal, *item)?;
                }
            }
            Expr::Record { fields, spread } => {
                for (_, field) in fields {
                    self.select_expr(source, internal, *field)?;
                }
                if let RecordSpread::Head(item) | RecordSpread::Tail(item) = spread {
                    self.select_expr(source, internal, *item)?;
                }
            }
            Expr::Select(receiver, select) => {
                self.select_expr(source, internal, *receiver)?;
                self.select_select(*select);
            }
            Expr::Case(scrutinee, arms) => {
                self.select_expr(source, internal, *scrutinee)?;
                for arm in arms {
                    self.select_pat(source, internal, arm.pat)?;
                    if let Some(guard) = arm.guard {
                        self.select_expr(source, internal, guard)?;
                    }
                    self.select_expr(source, internal, arm.body)?;
                }
            }
            Expr::Catch(body, arms) => {
                self.select_expr(source, internal, *body)?;
                for arm in arms {
                    self.select_pat(source, internal, arm.pat)?;
                    if let Some(continuation) = arm.continuation {
                        self.select_pat(source, internal, continuation)?;
                    }
                    if let Some(guard) = arm.guard {
                        self.select_expr(source, internal, guard)?;
                    }
                    self.select_expr(source, internal, arm.body)?;
                }
            }
            Expr::Block(stmts, result) => {
                for stmt in stmts {
                    self.select_stmt(source, internal, stmt)?;
                }
                if let Some(result) = result {
                    self.select_expr(source, internal, *result)?;
                }
            }
        }
        Ok(())
    }

    fn select_stmt(
        &mut self,
        source: &PolyArena,
        internal: &mut FxHashSet<DefId>,
        stmt: &Stmt,
    ) -> Result<(), TypedActBodyError> {
        match stmt {
            Stmt::Let(_, pat, expr) => {
                self.select_pat(source, internal, *pat)?;
                self.select_expr(source, internal, *expr)?;
            }
            Stmt::Expr(expr) => self.select_expr(source, internal, *expr)?,
            Stmt::Module(def, stmts) => {
                add_internal_def_closure(source, internal, *def)?;
                self.select_def(source, internal, *def)?;
                for stmt in stmts {
                    self.select_stmt(source, internal, stmt)?;
                }
            }
        }
        Ok(())
    }

    fn select_pat(
        &mut self,
        source: &PolyArena,
        internal: &mut FxHashSet<DefId>,
        pat: PatId,
    ) -> Result<(), TypedActBodyError> {
        if !self.pats.insert(pat) {
            return Ok(());
        }
        match source.pat(pat) {
            Pat::Wild | Pat::Lit(_) => {}
            Pat::Tuple(items) | Pat::PolyVariant(_, items) => {
                for item in items {
                    self.select_pat(source, internal, *item)?;
                }
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => {
                for item in prefix.iter().chain(spread).chain(suffix) {
                    self.select_pat(source, internal, *item)?;
                }
            }
            Pat::Record { fields, spread } => {
                for field in fields {
                    self.select_pat(source, internal, field.pat)?;
                    if let Some(default) = field.default {
                        self.select_expr(source, internal, default)?;
                    }
                }
                if let RecordSpread::Head(Some(def)) | RecordSpread::Tail(Some(def)) = spread {
                    add_internal_def_closure(source, internal, *def)?;
                    self.select_def(source, internal, *def)?;
                }
            }
            Pat::Con(reference, payloads) => {
                self.select_ref(source, *reference);
                for payload in payloads {
                    self.select_pat(source, internal, *payload)?;
                }
            }
            Pat::Ref(reference) => self.select_ref(source, *reference),
            Pat::Var(def) => {
                add_internal_def_closure(source, internal, *def)?;
                self.select_def(source, internal, *def)?;
            }
            Pat::Or(left, right) => {
                self.select_pat(source, internal, *left)?;
                self.select_pat(source, internal, *right)?;
            }
            Pat::As(inner, def) => {
                self.select_pat(source, internal, *inner)?;
                add_internal_def_closure(source, internal, *def)?;
                self.select_def(source, internal, *def)?;
            }
        }
        Ok(())
    }
}

fn add_internal_def_closure(
    source: &PolyArena,
    internal: &mut FxHashSet<DefId>,
    root: DefId,
) -> Result<(), TypedActBodyError> {
    let mut pending = vec![root];
    while let Some(def) = pending.pop() {
        if !internal.insert(def) {
            continue;
        }
        let item = source
            .defs
            .get(def)
            .ok_or(TypedActBodyError::MissingDefinition(def))?;
        match item {
            Def::Mod { children, .. } | Def::Let { children, .. } => {
                pending.extend(children.iter().copied());
            }
            Def::Arg => {}
        }
    }
    Ok(())
}

#[derive(Default)]
struct BodyIds {
    defs: FxHashMap<DefId, DefId>,
    exprs: FxHashMap<ExprId, ExprId>,
    pats: FxHashMap<PatId, PatId>,
    refs: FxHashMap<RefId, RefId>,
    selects: FxHashMap<SelectId, SelectId>,
}

impl BodyIds {
    fn def(&self, id: DefId) -> DefId {
        self.defs[&id]
    }
    fn expr(&self, id: ExprId) -> ExprId {
        self.exprs[&id]
    }
    fn pat(&self, id: PatId) -> PatId {
        self.pats[&id]
    }
    fn reference(&self, id: RefId) -> RefId {
        self.refs[&id]
    }
    fn select(&self, id: SelectId) -> SelectId {
        self.selects[&id]
    }
}

struct BodyImporter<'a> {
    source: &'a PolyArena,
    selection: &'a BodySelection,
    paths: &'a FxHashMap<Vec<String>, Vec<String>>,
    target: PolyArena,
    labels: DumpLabels,
    ids: BodyIds,
    external_refs: FxHashMap<RefId, StableExternalReferenceKey>,
    external_selects: FxHashMap<SelectId, StableExternalReferenceKey>,
    external_catches: FxHashMap<CatchSite, StableExternalReferenceKey>,
}

impl<'a> BodyImporter<'a> {
    fn new(
        source: &'a PolyArena,
        selection: &'a BodySelection,
        paths: &'a FxHashMap<Vec<String>, Vec<String>>,
    ) -> Self {
        Self {
            source,
            selection,
            paths,
            target: PolyArena::new(),
            labels: DumpLabels::new(),
            ids: BodyIds::default(),
            external_refs: FxHashMap::default(),
            external_selects: FxHashMap::default(),
            external_catches: FxHashMap::default(),
        }
    }

    fn reserve(&mut self) {
        let mut defs = self.selection.defs.iter().copied().collect::<Vec<_>>();
        defs.sort_by_key(|id| id.0);
        for id in defs {
            self.ids.defs.insert(id, self.target.defs.fresh());
        }
        let mut exprs = self.selection.exprs.iter().copied().collect::<Vec<_>>();
        exprs.sort_by_key(|id| id.0);
        for id in exprs {
            self.ids.exprs.insert(id, self.target.reserve_expr_slot());
        }
        let mut pats = self.selection.pats.iter().copied().collect::<Vec<_>>();
        pats.sort_by_key(|id| id.0);
        for id in pats {
            self.ids.pats.insert(id, self.target.reserve_pat_slot());
        }
        let mut refs = self.selection.refs.iter().copied().collect::<Vec<_>>();
        refs.sort_by_key(|id| id.0);
        for id in refs {
            self.ids.refs.insert(id, self.target.add_ref());
        }
        let mut selects = self.selection.selects.iter().copied().collect::<Vec<_>>();
        selects.sort_by_key(|id| id.0);
        for id in selects {
            self.ids.selects.insert(
                id,
                self.target.add_select(self.source.select(id).name.clone()),
            );
        }
    }

    fn capture_external_targets(
        &mut self,
        modules: &ModuleTable,
        internal: &FxHashSet<DefId>,
    ) -> Result<(), TypedActBodyError> {
        for reference in &self.selection.refs {
            let target = self
                .source
                .ref_target(*reference)
                .ok_or(TypedActBodyError::MissingReferenceTarget(*reference))?;
            if !internal.contains(&target) {
                let key = modules
                    .stable_external_reference_key(target)
                    .ok_or(TypedActBodyError::MissingExternalKey(target))?;
                self.external_refs
                    .insert(self.ids.reference(*reference), key);
            }
        }
        for select in &self.selection.selects {
            let target = match self.source.select(*select).resolution {
                Some(SelectResolution::Method { def }) => Some(def),
                Some(SelectResolution::TypeclassMethod { member }) => Some(member),
                Some(SelectResolution::RecordField) => None,
                None => return Err(TypedActBodyError::MissingSelectionTarget(*select)),
            };
            if let Some(target) = target.filter(|target| !internal.contains(target)) {
                let key = modules
                    .stable_external_reference_key(target)
                    .ok_or(TypedActBodyError::MissingExternalKey(target))?;
                self.external_selects.insert(self.ids.select(*select), key);
            }
        }
        for expr in &self.selection.exprs {
            let Expr::Catch(_, arms) = self.source.expr(*expr) else {
                continue;
            };
            for (arm, operation) in arms
                .iter()
                .enumerate()
                .filter_map(|(index, arm)| arm.operation.as_ref().map(|op| (index, op)))
            {
                if operation.def.is_some_and(|def| internal.contains(&def)) {
                    continue;
                }
                let key = operation
                    .def
                    .and_then(|def| modules.stable_external_reference_key(def))
                    .or_else(|| modules.stable_operation_reference_key(&operation.path))
                    .ok_or_else(|| {
                        TypedActBodyError::MissingExternalOperationPath(operation.path.clone())
                    })?;
                self.external_catches.insert(
                    CatchSite {
                        expr: self.ids.expr(*expr),
                        arm,
                    },
                    key,
                );
            }
        }
        Ok(())
    }

    fn import_nodes(&mut self) -> Result<(), TypedActBodyError> {
        let mut types = std::mem::replace(&mut self.target.typ, poly::types::TypeArena::new());
        let mut type_cloner =
            NominalTypeGraphCloner::new(&self.source.typ, &mut types, self.paths, None);
        for source_id in sorted(&self.selection.defs, |id| id.0) {
            let def = self
                .source
                .defs
                .get(source_id)
                .ok_or(TypedActBodyError::MissingDefinition(source_id))?;
            let cloned = match def {
                Def::Mod { vis, children } => Def::Mod {
                    vis: *vis,
                    children: children.iter().map(|id| self.ids.def(*id)).collect(),
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
                        .map(|scheme| type_cloner.clone_scheme(scheme)),
                    body: body.map(|id| self.ids.expr(id)),
                    children: children.iter().map(|id| self.ids.def(*id)).collect(),
                },
                Def::Arg => Def::Arg,
            };
            self.target.defs.set(self.ids.def(source_id), cloned);
        }
        drop(type_cloner);
        self.target.typ = types;
        for source_id in sorted(&self.selection.refs, |id| id.0) {
            if self
                .external_refs
                .contains_key(&self.ids.reference(source_id))
            {
                continue;
            }
            let target = self
                .source
                .ref_target(source_id)
                .ok_or(TypedActBodyError::MissingReferenceTarget(source_id))?;
            self.target
                .resolve_ref(self.ids.reference(source_id), self.ids.def(target));
        }
        for source_id in sorted(&self.selection.selects, |id| id.0) {
            if self
                .external_selects
                .contains_key(&self.ids.select(source_id))
            {
                continue;
            }
            if let Some(resolution) = self.source.select(source_id).resolution {
                let resolution = match resolution {
                    SelectResolution::RecordField => SelectResolution::RecordField,
                    SelectResolution::Method { def } => SelectResolution::Method {
                        def: self.ids.def(def),
                    },
                    SelectResolution::TypeclassMethod { member } => {
                        SelectResolution::TypeclassMethod {
                            member: self.ids.def(member),
                        }
                    }
                };
                self.target
                    .resolve_select(self.ids.select(source_id), resolution);
            }
        }
        for source_id in sorted(&self.selection.exprs, |id| id.0) {
            let cloned = self.clone_expr(source_id);
            self.target.set_expr(self.ids.expr(source_id), cloned);
        }
        for source_id in sorted(&self.selection.pats, |id| id.0) {
            let cloned = self.clone_pat(self.source.pat(source_id));
            self.target.set_pat(self.ids.pat(source_id), cloned);
        }
        Ok(())
    }

    fn clone_expr(&self, source_id: ExprId) -> Expr {
        match self.source.expr(source_id) {
            Expr::Lit(lit) => Expr::Lit(lit.clone()),
            Expr::PrimitiveOp(op) => Expr::PrimitiveOp(*op),
            Expr::Var(id) => Expr::Var(self.ids.reference(*id)),
            Expr::App(a, b) => Expr::App(self.ids.expr(*a), self.ids.expr(*b)),
            Expr::RefSet(a, b) => Expr::RefSet(self.ids.expr(*a), self.ids.expr(*b)),
            Expr::Lambda(pat, body) => Expr::Lambda(self.ids.pat(*pat), self.ids.expr(*body)),
            Expr::Tuple(items) => Expr::Tuple(items.iter().map(|id| self.ids.expr(*id)).collect()),
            Expr::Record { fields, spread } => Expr::Record {
                fields: fields
                    .iter()
                    .map(|(name, id)| (name.clone(), self.ids.expr(*id)))
                    .collect(),
                spread: self.clone_expr_spread(spread),
            },
            Expr::PolyVariant(name, items) => Expr::PolyVariant(
                name.clone(),
                items.iter().map(|id| self.ids.expr(*id)).collect(),
            ),
            Expr::Select(receiver, select) => {
                Expr::Select(self.ids.expr(*receiver), self.ids.select(*select))
            }
            Expr::Case(scrutinee, arms) => Expr::Case(
                self.ids.expr(*scrutinee),
                arms.iter()
                    .map(|arm| CaseArm {
                        pat: self.ids.pat(arm.pat),
                        guard: arm.guard.map(|id| self.ids.expr(id)),
                        body: self.ids.expr(arm.body),
                    })
                    .collect(),
            ),
            Expr::Catch(body, arms) => Expr::Catch(
                self.ids.expr(*body),
                arms.iter()
                    .enumerate()
                    .map(|(arm_index, arm)| CatchArm {
                        operation: arm.operation.as_ref().map(|operation| CatchOperation {
                            path: self.rewrite_path(&operation.path),
                            def: if self.external_catches.contains_key(&CatchSite {
                                expr: self.ids.expr(source_id),
                                arm: arm_index,
                            }) {
                                None
                            } else {
                                operation.def.map(|id| self.ids.def(id))
                            },
                        }),
                        pat: self.ids.pat(arm.pat),
                        continuation: arm.continuation.map(|id| self.ids.pat(id)),
                        guard: arm.guard.map(|id| self.ids.expr(id)),
                        body: self.ids.expr(arm.body),
                    })
                    .collect(),
            ),
            Expr::Block(stmts, result) => Expr::Block(
                stmts.iter().map(|stmt| self.clone_stmt(stmt)).collect(),
                result.map(|id| self.ids.expr(id)),
            ),
        }
    }

    fn clone_pat(&self, pat: &Pat) -> Pat {
        match pat {
            Pat::Wild => Pat::Wild,
            Pat::Lit(lit) => Pat::Lit(lit.clone()),
            Pat::Tuple(items) => Pat::Tuple(items.iter().map(|id| self.ids.pat(*id)).collect()),
            Pat::List {
                prefix,
                spread,
                suffix,
            } => Pat::List {
                prefix: prefix.iter().map(|id| self.ids.pat(*id)).collect(),
                spread: spread.map(|id| self.ids.pat(id)),
                suffix: suffix.iter().map(|id| self.ids.pat(*id)).collect(),
            },
            Pat::Record { fields, spread } => Pat::Record {
                fields: fields
                    .iter()
                    .map(|field| RecordPatField {
                        name: field.name.clone(),
                        pat: self.ids.pat(field.pat),
                        default: field.default.map(|id| self.ids.expr(id)),
                    })
                    .collect(),
                spread: self.clone_def_spread(spread),
            },
            Pat::PolyVariant(name, items) => Pat::PolyVariant(
                name.clone(),
                items.iter().map(|id| self.ids.pat(*id)).collect(),
            ),
            Pat::Con(reference, items) => Pat::Con(
                self.ids.reference(*reference),
                items.iter().map(|id| self.ids.pat(*id)).collect(),
            ),
            Pat::Ref(reference) => Pat::Ref(self.ids.reference(*reference)),
            Pat::Var(def) => Pat::Var(self.ids.def(*def)),
            Pat::Or(a, b) => Pat::Or(self.ids.pat(*a), self.ids.pat(*b)),
            Pat::As(pat, def) => Pat::As(self.ids.pat(*pat), self.ids.def(*def)),
        }
    }

    fn clone_stmt(&self, stmt: &Stmt) -> Stmt {
        match stmt {
            Stmt::Let(vis, pat, expr) => Stmt::Let(*vis, self.ids.pat(*pat), self.ids.expr(*expr)),
            Stmt::Expr(expr) => Stmt::Expr(self.ids.expr(*expr)),
            Stmt::Module(def, stmts) => Stmt::Module(
                self.ids.def(*def),
                stmts.iter().map(|stmt| self.clone_stmt(stmt)).collect(),
            ),
        }
    }

    fn clone_expr_spread(&self, spread: &RecordSpread<ExprId>) -> RecordSpread<ExprId> {
        match spread {
            RecordSpread::Head(id) => RecordSpread::Head(self.ids.expr(*id)),
            RecordSpread::Tail(id) => RecordSpread::Tail(self.ids.expr(*id)),
            RecordSpread::None => RecordSpread::None,
        }
    }

    fn clone_def_spread(
        &self,
        spread: &RecordSpread<Option<DefId>>,
    ) -> RecordSpread<Option<DefId>> {
        match spread {
            RecordSpread::Head(id) => RecordSpread::Head(id.map(|id| self.ids.def(id))),
            RecordSpread::Tail(id) => RecordSpread::Tail(id.map(|id| self.ids.def(id))),
            RecordSpread::None => RecordSpread::None,
        }
    }

    fn rewrite_path(&self, path: &[String]) -> Vec<String> {
        self.paths
            .get(path)
            .cloned()
            .unwrap_or_else(|| path.to_vec())
    }

    fn import_runtime_metadata(&mut self) {
        for (def, operation) in &self.source.effect_operations {
            if self.selection.defs.contains(def) {
                self.target.effect_operations.insert(
                    self.ids.def(*def),
                    poly::expr::EffectOperation {
                        path: self.rewrite_path(&operation.path),
                    },
                );
            }
        }
        for (def, constructor) in &self.source.constructors {
            if self.selection.defs.contains(def) {
                self.target.constructors.insert(
                    self.ids.def(*def),
                    poly::expr::Constructor {
                        owner_path: self.rewrite_path(&constructor.owner_path),
                        name: constructor.name.clone(),
                        arity: constructor.arity,
                    },
                );
            }
        }
        for (path, shape) in &self.source.nominal_record_shapes {
            if let Some(destination) = self.paths.get(path) {
                self.target.nominal_record_shapes.insert(
                    destination.clone(),
                    NominalRecordShape {
                        owner_path: destination.clone(),
                        fields: shape
                            .fields
                            .iter()
                            .map(|field| NominalRecordField {
                                name: field.name.clone(),
                                projection: self.ids.def(field.projection),
                            })
                            .collect(),
                    },
                );
            }
        }
        for def in &self.source.field_projections {
            if self.selection.defs.contains(def) {
                self.target.field_projections.insert(self.ids.def(*def));
            }
        }
        for path in &self.source.effect_family_paths {
            if let Some(destination) = self.paths.get(path) {
                self.target.effect_family_paths.insert(destination.clone());
            }
        }
    }

    fn import_labels(&mut self, source: &DumpLabels) {
        for (def, label) in source.def_labels() {
            if self.selection.defs.contains(&def) {
                self.labels.set_def_label(self.ids.def(def), label);
            }
        }
        for (reference, label) in source.ref_labels() {
            if self.selection.refs.contains(&reference) {
                self.labels
                    .set_ref_label(self.ids.reference(reference), label);
            }
        }
    }
}

fn sorted<T: Copy>(set: &FxHashSet<T>, key: impl Fn(&T) -> u32) -> Vec<T> {
    let mut out = set.iter().copied().collect::<Vec<_>>();
    out.sort_by_key(key);
    out
}
