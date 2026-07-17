use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use super::*;
use crate::analysis::{AnalysisTiming, Stage0PendingWorkInventory, Stage0QuantifyEvent};

#[test]
fn suffix_safety_stage0_paired_frontiers_are_characterized_before_generalization() {
    let prefix_loaded = repository_std_loaded("use std::prelude::*\nmod std;\n");
    let prefix = lower_loaded_files(&prefix_loaded)
        .expect("lower repository std prefix")
        .into_prefix();

    let cases = [
        Stage0Case::fixture("html", "std_prefix_yumark_html_fallback.yu", "proof"),
        Stage0Case::fixture(
            "markdown",
            "std_prefix_yumark_markdown_workload.yu",
            "proof",
        ),
        Stage0Case::fixture(
            "oracle-b-small",
            "std_prefix_oracle_b_small.yu",
            "oracle_b_result",
        ),
        Stage0Case {
            name: "ordinary-non-role",
            source: concat!(
                "use std::prelude::*\n",
                "mod std;\n",
                "my plain(value: int): int = value\n",
                "my proof(): int = plain 42\n",
                "proof()\n",
            )
            .to_string(),
            target: "proof",
        },
    ];
    let mut traces = BTreeMap::new();
    for case in cases {
        let trace = characterize_case(&prefix, &case);
        eprintln!("Stage 0 {}: {trace:#?}", case.name);
        traces.insert(case.name, trace);
    }

    let html = &traces["html"];
    let markdown = &traces["markdown"];
    for (route, trace) in [
        ("html cold", &html.cold),
        ("html warm", &html.warm),
        ("markdown cold", &markdown.cold),
        ("markdown warm", &markdown.warm),
    ] {
        assert_eq!(trace.route.quantified_components, 0, "{route}");
        assert!(trace.route.elapsed > Duration::ZERO, "{route}");
        assert!(trace.route.rounds > 0, "{route}");
        assert!(trace.route.routed_items > 0, "{route}");
        assert!(trace.route.open_uses <= trace.route.routed_items, "{route}");
        assert!(
            trace.route.instantiated_uses <= trace.route.routed_items,
            "{route}"
        );
        assert_eq!(trace.route.after.constraint_events, 0, "{route}");
        assert!(trace.route.after.def_finishes > 0, "{route}");
        assert!(trace.raw.target_roles.is_empty(), "{route}");
        assert!(trace.routed.target_roles.is_empty(), "{route}");
    }
    assert_eq!(html.cold.raw.target_root, markdown.cold.raw.target_root);
    assert_eq!(html.warm.raw.target_root, markdown.warm.raw.target_root);
    assert_eq!(
        html.cold.routed.target_root,
        markdown.cold.routed.target_root
    );
    assert_eq!(
        html.warm.routed.target_root,
        markdown.warm.routed.target_root
    );

    // The one extra HTML call produces a narrow queue-size delta, but the target graph remains
    // identical. Treating this source-shape count as a safety witness would not generalize.
    assert_eq!(
        html.cold.raw.pending.apply_refs,
        markdown.cold.raw.pending.apply_refs + 1
    );
    assert_eq!(
        html.warm.raw.pending.apply_refs,
        markdown.warm.raw.pending.apply_refs + 1
    );

    // Even the last read-only point before `proof` generalizes contains no cold/warm delta in
    // these structural facts. HTML and Markdown differ from each other (format/repr and root
    // shape), but each suffix has the same counterfactual/canonical view, so that pair identity is
    // not a route-safety witness.
    assert_same_quantify_shape(
        "html",
        &html.cold.completed.quantify,
        &html.warm.completed.quantify,
    );
    assert_same_quantify_shape(
        "markdown",
        &markdown.cold.completed.quantify,
        &markdown.warm.completed.quantify,
    );
    assert_eq!(html.cold.completed.quantify.root_variables, 16);
    assert_eq!(markdown.cold.completed.quantify.root_variables, 13);
    for trace in [
        &html.cold.completed.quantify,
        &html.warm.completed.quantify,
        &markdown.cold.completed.quantify,
        &markdown.warm.completed.quantify,
    ] {
        assert_eq!(trace.roles.len(), 1);
        assert_eq!(trace.role_variables, 61);
        assert_eq!(trace.shared_variables, 0);
        assert_eq!(trace.role_only_variables, 61);
    }

    let oracle_b = &traces["oracle-b-small"];
    assert_same_quantify_shape(
        "oracle-b-small",
        &oracle_b.cold.completed.quantify,
        &oracle_b.warm.completed.quantify,
    );
    let ordinary = &traces["ordinary-non-role"];
    assert_same_quantify_shape(
        "ordinary-non-role",
        &ordinary.cold.completed.quantify,
        &ordinary.warm.completed.quantify,
    );
    assert!(ordinary.cold.completed.quantify.roles.is_empty());
    assert!(ordinary.warm.completed.quantify.roles.is_empty());
    for trace in traces.values().flat_map(|trace| [&trace.cold, &trace.warm]) {
        assert!(trace.completed.shallow_lowering > Duration::ZERO);
        assert!(trace.completed.drain > Duration::ZERO);
        assert!(trace.completed.resolve_remaining_selections > Duration::ZERO);
        assert!(trace.completed.quantify_generalize > Duration::ZERO);
        assert!(trace.completed.role_resolution > Duration::ZERO);
        assert!(trace.completed.quantified_components > 0);
        assert!(trace.completed.quantify.quantified_components_before > 0);
        assert_eq!(trace.completed.diagnostics, 0);
    }
}

fn assert_same_quantify_shape(
    name: &str,
    cold: &Stage0QuantifyFrontier,
    warm: &Stage0QuantifyFrontier,
) {
    assert_eq!(cold.component_size, warm.component_size, "{name}");
    assert_eq!(cold.root, warm.root, "{name}");
    assert_eq!(cold.roles, warm.roles, "{name}");
    assert_eq!(cold.root_variables, warm.root_variables, "{name}");
    assert_eq!(cold.role_variables, warm.role_variables, "{name}");
    assert_eq!(cold.shared_variables, warm.shared_variables, "{name}");
    assert_eq!(cold.role_only_variables, warm.role_only_variables, "{name}");
}

struct Stage0Case {
    name: &'static str,
    source: String,
    target: &'static str,
}

impl Stage0Case {
    fn fixture(name: &'static str, fixture: &str, target: &'static str) -> Self {
        Self {
            name,
            source: fixture_source(fixture),
            target,
        }
    }
}

#[derive(Debug)]
struct Stage0CaseTrace {
    cold: Stage0WorldTrace,
    warm: Stage0WorldTrace,
}

#[derive(Debug)]
struct Stage0WorldTrace {
    raw: Stage0Frontier,
    route: Stage0RouteTrace,
    routed: Stage0Frontier,
    completed: Stage0CompletedTrace,
}

#[derive(Debug)]
struct Stage0RouteTrace {
    elapsed: Duration,
    rounds: usize,
    routed_items: usize,
    open_uses: usize,
    instantiated_uses: usize,
    quantified_components: usize,
    after: Stage0PendingWorkInventory,
}

#[derive(Debug)]
struct Stage0CompletedTrace {
    shallow_lowering: Duration,
    drain: Duration,
    resolve_remaining_selections: Duration,
    quantify_generalize: Duration,
    role_resolution: Duration,
    quantified_components: usize,
    quantify: Stage0QuantifyFrontier,
    diagnostics: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct Stage0QuantifyFrontier {
    component_size: usize,
    quantified_components_before: usize,
    root: StructuralStats,
    roles: Vec<RoleDemandStats>,
    root_variables: usize,
    role_variables: usize,
    shared_variables: usize,
    role_only_variables: usize,
}

impl Stage0QuantifyFrontier {
    fn from_event(event: &Stage0QuantifyEvent) -> Self {
        let root_variables = StructuralStats::variables_from_root(&event.root);
        let role_variables = event
            .roles
            .iter()
            .flat_map(|role| {
                role.inputs
                    .iter()
                    .map(|input| &input.bounds)
                    .chain(role.associated.iter().map(|item| &item.value.bounds))
            })
            .flat_map(StructuralStats::variables_from_bounds)
            .collect::<BTreeSet<_>>();
        let shared_variables = root_variables.intersection(&role_variables).count();
        let role_only_variables = role_variables.difference(&root_variables).count();
        Self {
            component_size: event.component.len(),
            quantified_components_before: event.quantified_components_before,
            root: StructuralStats::from_root(&event.root),
            roles: event
                .roles
                .iter()
                .map(RoleDemandStats::from_compact)
                .collect(),
            root_variables: root_variables.len(),
            role_variables: role_variables.len(),
            shared_variables,
            role_only_variables,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Stage0Frontier {
    pending: Stage0PendingWorkInventory,
    target_root: StructuralStats,
    target_roles: Vec<RoleDemandStats>,
}

impl Stage0Frontier {
    fn capture(lowerer: &BodyLowerer, target: &str) -> Self {
        let target = root_value_def(&lowerer.modules, target);
        let root = lowerer.typing.def(target).expect("target type root");
        let compact = compact_type_var(lowerer.session.infer.constraints(), root);
        let target_roles = lowerer
            .session
            .roles
            .for_owner(target)
            .iter()
            .map(|role| {
                RoleDemandStats::from_compact(&compact_role_constraint(
                    lowerer.session.infer.constraints(),
                    role,
                ))
            })
            .collect();
        Self {
            pending: lowerer.session.stage0_pending_work_inventory(),
            target_root: StructuralStats::from_root(&compact),
            target_roles,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RoleDemandStats {
    role: Vec<String>,
    input_stats: Vec<StructuralStats>,
    associated_stats: Vec<(String, StructuralStats)>,
}

impl RoleDemandStats {
    fn from_compact(role: &crate::compact::CompactRoleConstraint) -> Self {
        Self {
            role: role.role.clone(),
            input_stats: role
                .inputs
                .iter()
                .map(|input| StructuralStats::from_bounds(&input.bounds))
                .collect(),
            associated_stats: role
                .associated
                .iter()
                .map(|associated| {
                    (
                        associated.name.clone(),
                        StructuralStats::from_bounds(&associated.value.bounds),
                    )
                })
                .collect(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct StructuralStats {
    nodes: usize,
    variable_occurrences: usize,
    distinct_variables: usize,
    intervals: usize,
    functions: usize,
    records: usize,
    variants: usize,
    tuples: usize,
    constructors: BTreeMap<Vec<String>, usize>,
}

impl StructuralStats {
    fn variables_from_root(root: &CompactRoot) -> BTreeSet<u32> {
        let mut stats = Self::default();
        let mut variables = BTreeSet::new();
        stats.visit_type(&root.root, &mut variables);
        for recursive in &root.rec_vars {
            variables.insert(recursive.var.0);
            stats.visit_bounds(&recursive.bounds, &mut variables);
        }
        variables
    }

    fn variables_from_bounds(bounds: &CompactBounds) -> BTreeSet<u32> {
        let mut stats = Self::default();
        let mut variables = BTreeSet::new();
        stats.visit_bounds(bounds, &mut variables);
        variables
    }

    fn from_root(root: &CompactRoot) -> Self {
        let mut stats = Self::default();
        let variables = Self::variables_from_root(root);
        let mut visited_variables = BTreeSet::new();
        stats.visit_type(&root.root, &mut visited_variables);
        for recursive in &root.rec_vars {
            stats.visit_bounds(&recursive.bounds, &mut visited_variables);
        }
        stats.distinct_variables = variables.len();
        stats
    }

    fn from_bounds(bounds: &CompactBounds) -> Self {
        let mut stats = Self::default();
        let variables = Self::variables_from_bounds(bounds);
        let mut visited_variables = BTreeSet::new();
        stats.visit_bounds(bounds, &mut visited_variables);
        stats.distinct_variables = variables.len();
        stats
    }

    fn visit_type(&mut self, ty: &CompactType, variables: &mut BTreeSet<u32>) {
        self.nodes += 1;
        self.variable_occurrences += ty.vars.len();
        variables.extend(ty.vars.iter().map(|var| var.var.0));
        for (path, args) in &ty.cons {
            *self.constructors.entry(path.clone()).or_default() += 1;
            for arg in args {
                self.visit_bounds(arg, variables);
            }
        }
        for fun in &ty.funs {
            self.functions += 1;
            self.visit_type(&fun.arg, variables);
            self.visit_type(&fun.arg_eff, variables);
            self.visit_type(&fun.ret_eff, variables);
            self.visit_type(&fun.ret, variables);
        }
        for record in &ty.records {
            self.records += 1;
            for field in &record.fields {
                self.visit_type(&field.value, variables);
            }
        }
        for spread in &ty.record_spreads {
            self.records += 1;
            for field in &spread.fields {
                self.visit_type(&field.value, variables);
            }
            self.visit_type(&spread.tail, variables);
        }
        for variant in &ty.poly_variants {
            self.variants += 1;
            for (_, payload) in &variant.items {
                for item in payload {
                    self.visit_type(item, variables);
                }
            }
        }
        for tuple in &ty.tuples {
            self.tuples += 1;
            for item in &tuple.items {
                self.visit_type(item, variables);
            }
        }
        for row in &ty.rows {
            for args in row.items.values() {
                for arg in args {
                    self.visit_bounds(arg, variables);
                }
            }
            self.visit_type(&row.tail, variables);
        }
    }

    fn visit_bounds(&mut self, bounds: &CompactBounds, variables: &mut BTreeSet<u32>) {
        self.nodes += 1;
        match bounds {
            CompactBounds::Interval { lower, upper } => {
                self.intervals += 1;
                self.visit_type(lower, variables);
                self.visit_type(upper, variables);
            }
            CompactBounds::Con { path, args } => {
                *self.constructors.entry(path.clone()).or_default() += 1;
                for arg in args {
                    self.visit_bounds(arg, variables);
                }
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.functions += 1;
                self.visit_bounds(arg, variables);
                self.visit_bounds(arg_eff, variables);
                self.visit_bounds(ret_eff, variables);
                self.visit_bounds(ret, variables);
            }
            CompactBounds::Record { fields } => {
                self.records += 1;
                for field in fields {
                    self.visit_bounds(&field.value, variables);
                }
            }
            CompactBounds::PolyVariant { items } => {
                self.variants += 1;
                for (_, payload) in items {
                    for item in payload {
                        self.visit_bounds(item, variables);
                    }
                }
            }
            CompactBounds::Tuple { items } => {
                self.tuples += 1;
                for item in items {
                    self.visit_bounds(item, variables);
                }
            }
        }
    }
}

fn characterize_case(prefix: &BodyLoweringPrefix, case: &Stage0Case) -> Stage0CaseTrace {
    Stage0CaseTrace {
        cold: characterize_world(
            prepare_cold(&case.source),
            prepare_cold(&case.source),
            case.target,
        ),
        warm: characterize_world(
            prepare_warm(prefix, &case.source),
            prepare_warm(prefix, &case.source),
            case.target,
        ),
    }
}

fn characterize_world(
    mut frontier: PreparedLowering,
    completed: PreparedLowering,
    target: &str,
) -> Stage0WorldTrace {
    let raw = Stage0Frontier::capture(&frontier.lowerer, target);
    let route = frontier.lowerer.session.stage0_route_non_quantifying_work();
    let route = Stage0RouteTrace {
        elapsed: route.elapsed,
        rounds: route.rounds,
        routed_items: route.routed_items,
        open_uses: route.open_uses,
        instantiated_uses: route.instantiated_uses,
        quantified_components: route.quantified_components,
        after: route.after,
    };
    let routed = Stage0Frontier::capture(&frontier.lowerer, target);
    Stage0WorldTrace {
        raw,
        route,
        routed,
        completed: complete_world(completed, target),
    }
}

fn complete_world(mut prepared: PreparedLowering, target: &str) -> Stage0CompletedTrace {
    let target = root_value_def(&prepared.lowerer.modules, target);
    prepared.lowerer.session.stage0_watch_quantify_def(target);

    let start = Instant::now();
    prepared.lowerer.drain_analysis_with_conformance();
    let drain = start.elapsed();

    let start = Instant::now();
    prepared
        .lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let resolve_remaining_selections = start.elapsed();

    let events = prepared.lowerer.session.stage0_take_quantify_events();
    let [event] = events.as_slice() else {
        panic!(
            "expected one target quantification event, got {}",
            events.len()
        )
    };
    assert_eq!(event.def, target);
    let quantify = Stage0QuantifyFrontier::from_event(event);
    let timing: AnalysisTiming = prepared.lowerer.session.timing();
    let output = prepared.lowerer.finish();
    Stage0CompletedTrace {
        shallow_lowering: prepared.shallow_lowering,
        drain,
        resolve_remaining_selections,
        quantify_generalize: timing.quantify_generalize,
        role_resolution: timing.generalize_resolve_roles + timing.method_role_solve,
        quantified_components: timing.quantified_components,
        quantify,
        diagnostics: output.errors.len(),
    }
}

struct PreparedLowering {
    lowerer: BodyLowerer,
    shallow_lowering: Duration,
}

fn prepare_cold(source: &str) -> PreparedLowering {
    let loaded = repository_std_loaded(source);
    prepare_loaded_files(&loaded)
}

fn prepare_warm(prefix: &BodyLoweringPrefix, source: &str) -> PreparedLowering {
    let suffix = sources::load(vec![source_file(&[], source)]);
    let append = append_loaded_files_to_lower(
        Lower {
            arena: prefix.poly.clone(),
            modules: prefix.modules.clone(),
            source_file: Path::default(),
            source_text: None,
        },
        &suffix,
    )
    .expect("append suffix to repository std prefix");
    let mut lowerer = BodyLowerer::new_with_imported_boundary(append.lower, &prefix.boundary);
    lowerer.prefix_runtime = prefix.runtime.clone();
    let suffix_labels = lowerer.labels.clone();
    lowerer.labels = prefix.labels.clone();
    lowerer.labels.extend(suffix_labels);
    lowerer.errors.extend(prefix.errors.clone());
    let start = Instant::now();
    lower_loaded_file_bodies(&mut lowerer, &append.loaded);
    lowerer.lower_synthetic_act_copy_bodies_for(
        append.synthetic_var_act_copy_ids,
        append.synthetic_sub_label_act_copy_ids,
    );
    let shallow_lowering = start.elapsed();
    assert!(lowerer.errors.is_empty(), "warm: {:?}", lowerer.errors);
    PreparedLowering {
        lowerer,
        shallow_lowering,
    }
}

fn prepare_loaded_files(files: &[LoadedFile]) -> PreparedLowering {
    let loaded = LoadedFileCsts::new(files).expect("index loaded files");
    let lower = lower_loaded_file_csts_module_map(&loaded).expect("lower module map");
    let mut lowerer = BodyLowerer::new(lower);
    let start = Instant::now();
    lower_loaded_file_bodies(&mut lowerer, &loaded);
    lowerer.lower_synthetic_act_copy_bodies();
    let shallow_lowering = start.elapsed();
    assert!(lowerer.errors.is_empty(), "cold: {:?}", lowerer.errors);
    PreparedLowering {
        lowerer,
        shallow_lowering,
    }
}

fn lower_loaded_file_bodies(lowerer: &mut BodyLowerer, loaded: &LoadedFileCsts) {
    for file in loaded.by_depth() {
        let module = lowerer
            .modules
            .module_by_path(&file.module_path)
            .expect("loaded module path");
        let previous_source_file =
            std::mem::replace(&mut lowerer.source_file, file.module_path.clone());
        lowerer.lower_block(&file.cst, module);
        lowerer.source_file = previous_source_file;
    }
}

pub(super) fn repository_std_loaded(root_source: &str) -> Vec<LoadedFile> {
    let repository = repository_root();
    let lib = repository.join("lib");
    let mut paths = vec![lib.join("std.yu")];
    collect_yu_files(&lib.join("std"), &mut paths);
    paths.sort();

    let mut files = vec![source_file(&[], root_source)];
    files.extend(paths.into_iter().map(|path| {
        let relative = path.strip_prefix(&lib).expect("std path below lib");
        let mut module = relative.to_path_buf();
        module.set_extension("");
        let segments = module
            .components()
            .map(|component| {
                let std::path::Component::Normal(segment) = component else {
                    panic!("normal std module path component")
                };
                segment.to_str().expect("utf-8 std path")
            })
            .collect::<Vec<_>>();
        source_file(
            &segments,
            &fs::read_to_string(path).expect("read std source"),
        )
    }));
    sources::load(files)
}

pub(super) fn root_value_def(modules: &ModuleTable, name: &str) -> DefId {
    let decls = modules.value_decls(modules.root_id(), &Name(name.into()));
    let [decl] = decls.as_slice() else {
        panic!("expected one root value {name:?}")
    };
    decl.def
}

pub(super) fn fixture_source(name: &str) -> String {
    let path = repository_root()
        .join("tests/yulang/regressions/cache")
        .join(name);
    format!(
        "use std::prelude::*\nmod std;\n{}",
        fs::read_to_string(path).expect("read Stage 0 fixture")
    )
}

fn repository_root() -> PathBuf {
    FsPath::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonical repository root")
}

fn collect_yu_files(directory: &FsPath, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("read repository std directory") {
        let path = entry.expect("read repository std entry").path();
        if path.is_dir() {
            collect_yu_files(&path, files);
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("yu") {
            files.push(path);
        }
    }
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path {
            segments: path
                .iter()
                .map(|segment| sources::Name((*segment).to_string()))
                .collect(),
        },
        source: source.to_string(),
    }
}
