# Yulang Infer Export Subsystem — Code Smell Report

型推論結果を外部表現に変換する export サブシステムは、段階的な拡張を重ねてきたもので、5200行超の principal.rs と complete_principal.rs に相互依存と構造的な重複が蓄積している。特に「完全な」型推論キャッシュとのバランスをとるため、ほぼ同じロジックが複数の場所に分散している。以下は最も悪い匂いのスポット。

---

## 1. principal.rs と complete_principal.rs の明らかな並列構造

- **場所**: `crates/yulang-infer/src/export/principal.rs:8-12, 1147-1245` vs `crates/yulang-infer/src/export/complete_principal.rs:40-160, 707-770`
- **匂い**: 大規模なファイル間での概念的重複（並列ロジック）

principal.rs の export_principal_binding と complete_principal.rs の apply_principal_substitutions_from_parts は、同じ型推論ステップを別な粒度で解いている。両者とも:

```rust
// principal.rs, 1147-1245
pub(crate) fn export_principal_binding(
    state: &LowerState,
    globals: &HashMap<DefId, Path>,
    principal_scheme_cache: &mut HashMap<DefId, Option<typed_ir::Scheme>>,
    base_bounds_cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
    complete_principal_cache: &mut CompletePrincipalCache,
    profile: Option<&mut ExprExportProfile>,
    path: &Path,
    def: DefId,
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Option<typed_ir::PrincipalBinding> {
    // ... 5 levels of nested Option/match handling
    let (scheme, relevant_vars) = if let Some(scheme) = state.compact_scheme_of(def) {
        let relevant_vars = export_scheme_body_type_vars(&scheme);
        if should_prefer_frozen_runtime_scheme(path, &relevant_vars) {
            if let Some(frozen) = frozen_scheme.as_ref() {
                // path A: frozen
            } else {
                // path B: compact constraints
            }
        } else {
            // path C: normal export
        }
    } else {
        if let Some(frozen) = frozen_scheme.as_ref() {
            // path D: frozen fallback
        } else {
            // path E: coalesced fallback
        }
    };
```

vs

```rust
// complete_principal.rs, 707-770
fn apply_principal_substitutions_from_parts(
    // ... 10 parameters
    slot_bounds: &ApplySlotBounds,
    mut base_bounds_cache: Option<&mut HashMap<TypeVar, typed_ir::TypeBounds>>,
    cache: &mut CompletePrincipalCache,
    mut profile: Option<&mut CompletePrincipalStepProfile>,
) -> Vec<typed_ir::TypeSubstitution> {
    let mut unifier = PrincipalSubstitutionUnifier::new(&params);
    // ... similar Option chains with profile.as_deref_mut()
    if !unifier.covers_params() {
        if let Some(arg_ty) = export_monomorphic_type_for_tv_cached(...) {
            unifier.infer_value(param, &arg_ty);
        }
    }
    // ... more unifier work
}
```

**所感**: 両者は同じ推論キャッシュ (`complete_principal_cache`) に依存しながら、別な API で露出している。統合できるかもね。

---

## 2. export_bindings_for_paths と complete_referenced_binding_closure のコード重複

- **場所**: `crates/yulang-infer/src/export/principal.rs:811-929` vs `crates/yulang-infer/src/export/paths.rs:64-159`
- **匂い**: ほぼ同じ binding export ループ、別の文脈で実装

```rust
// principal.rs, 811-929
fn export_bindings_for_paths(
    state: &mut LowerState,
    paths: &[(Path, DefId)],
    extra_exprs: &[typed_ir::Expr],
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Vec<typed_ir::PrincipalBinding> {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let t_canonical = ExportClock::now(export_timing);
    let canonical = collect_canonical_binding_paths(state);
    // ... 10 lines of profiling ...
    let mut bindings = Vec::new();
    for (def, path) in canonical {
        if !target_def_set.contains(&def) {
            continue;
        }
        let t_binding = ExportClock::now(export_timing);
        if let Some(binding) = export_principal_binding(
            state, &globals, &mut principal_scheme_cache,
            &mut base_bounds_cache, &mut complete_principal_cache,
            expr_profile.as_mut(), &path, def, edge_evidence,
        ) {
            binding_times.push((binding.name.clone(), t_binding.elapsed(), expr_profile));
            bindings.push(binding);
        }
    }
    dedup_bindings_by_runtime_path(&mut bindings);
    bindings
}
```

vs

```rust
// paths.rs, 64-159
pub(crate) fn complete_referenced_binding_closure(
    state: &mut LowerState,
    globals: &HashMap<DefId, Path>,
    // ... same caches ...
    bindings: &mut Vec<typed_ir::PrincipalBinding>,
    extra_exprs: &[typed_ir::Expr],
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let all_paths = globals
        .iter()
        .map(|(def, path)| (export_path(path), (path.clone(), *def)))
        .collect::<HashMap<_, _>>();
    let mut binding_times = Vec::new();
    while !pending_refs.is_empty() {
        let pending = std::mem::take(&mut pending_refs);
        for path in pending {
            if exported.contains(&path) {
                continue;
            }
            let Some((source_path, def)) = all_paths.get(&path).cloned() else {
                continue;
            };
            let started = PathExportClock::now(export_timing);
            let Some(binding) = export_principal_binding(
                state, globals, principal_scheme_cache,
                base_bounds_cache, complete_principal_cache,
                expr_profile.as_mut(), &source_path, def, edge_evidence,
            ) else {
                continue;
            };
            binding_times.push((binding.name.clone(), started.elapsed(), expr_profile));
        }
    }
}
```

**所感**: 同じプロファイリング string と `binding_times` ベクタを繰り返している。抽出してもいいかも。

---

## 3. erase_open_vars_from_runtime_type の深いネスト＆複数の mutually-recursive 関数

- **場所**: `crates/yulang-infer/src/export/principal.rs:545-628`
- **匂い**: 84行の match 式、5段階のネスト、再帰、`.unwrap_or(Type::Unknown)` 繰り返し

```rust
fn erase_open_vars_from_runtime_type(ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Var(_) => None,
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Named { .. } => Some(erase_open_vars_from_type_arg_type(ty)),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(typed_ir::Type::Fun {
            param: Box::new(
                erase_open_vars_from_runtime_type(param).unwrap_or(typed_ir::Type::Unknown),
            ),
            param_effect: Box::new(
                erase_open_vars_from_runtime_type(param_effect).unwrap_or(typed_ir::Type::Unknown),
            ),
            ret_effect: Box::new(
                erase_open_vars_from_runtime_type(ret_effect).unwrap_or(typed_ir::Type::Unknown),
            ),
            ret: Box::new(
                erase_open_vars_from_runtime_type(ret).unwrap_or(typed_ir::Type::Unknown),
            ),
        }),
        typed_ir::Type::Tuple(items) => Some(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| {
                    erase_open_vars_from_runtime_type(item).unwrap_or(typed_ir::Type::Unknown)
                })
                .collect(),
        )),
        // ... 30+ more lines with Record, Variant, Row, Union, Inter, Recursive
    }
}

fn erase_open_vars_from_type_arg_type(ty: &typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(
                        erase_open_vars_from_runtime_type(ty).unwrap_or(typed_ir::Type::Unknown),
                    ),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        let lower = bounds
                            .lower
                            .as_deref()
                            .and_then(erase_open_vars_from_runtime_type);
                        // ...
                    }
                    _ => arg.clone(),
                })
                .collect(),
        },
        _ => ty.clone(),
    }
}

fn erase_open_vars_from_runtime_type_list(
    items: &[typed_ir::Type],
    is_union: bool,
) -> Option<typed_ir::Type> {
    // ...
}
```

**所感**: 型構造の再帰を 3 つの関数に分割しているけど、つながりが弱い。helper を作ってもいいかも。

---

## 4. export_principal_binding の 5 段階の条件分岐（frozen_scheme 優先判定）

- **場所**: `crates/yulang-infer/src/export/principal.rs:1179-1230`
- **匂い**: 条件分岐の深さ、frozen_scheme 有無の判定が複数回出現

```rust
    let frozen_scheme = state.infer.frozen_schemes.borrow().get(&def).cloned();
    let (scheme, relevant_vars) = if let Some(scheme) = state.compact_scheme_of(def) {
        let relevant_vars = export_scheme_body_type_vars(&scheme);
        if should_prefer_frozen_runtime_scheme(path, &relevant_vars) {
            if let Some(frozen) = frozen_scheme.as_ref() {
                (
                    export_frozen_scheme(&state.infer, frozen),
                    export_frozen_scheme_body_type_vars(&state.infer, frozen),
                )
            } else {
                let constraints = state.infer.compact_role_constraints_of(def);
                (
                    export_scheme(&state.infer, &scheme, &constraints),
                    relevant_vars,
                )
            }
        } else {
            let constraints = state.infer.compact_role_constraints_of(def);
            (
                export_scheme(&state.infer, &scheme, &constraints),
                relevant_vars,
            )
        }
    } else {
        if let Some(frozen) = frozen_scheme.as_ref() {
            (
                export_frozen_scheme(&state.infer, frozen),
                export_frozen_scheme_body_type_vars(&state.infer, frozen),
            )
        } else {
            let fallback_scheme = state
                .def_tvs
                .get(&def)
                .copied()
                .map(|tv| coalesce_by_co_occurrence(&compact_type_var(&state.infer, tv)));
            let fallback_body = fallback_scheme
                .as_ref()
                .map(export_scheme_body)
                .unwrap_or(typed_ir::Type::Unknown);
            let relevant_vars = fallback_scheme
                .as_ref()
                .map(export_scheme_body_type_vars)
                .unwrap_or_default();
            (
                typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: fallback_body,
                },
                relevant_vars,
            )
        }
    };
```

**所感**: スキーム選択ロジックを別関数に抽出してもいいかも。5段階は多い。

---

## 5. ExprExporter への大量のミュータブルキャッシュ参照

- **場所**: `crates/yulang-infer/src/export/expr.rs:310-335`
- **匂い**: 8個のミュータブルハッシュマップ/キャッシュを構造体メンバにもち、clear()できない不変数

```rust
impl<'a> ExprExporter<'a> {
    pub(super) fn new(
        state: &'a LowerState,
        globals: &'a HashMap<DefId, Path>,
        principal_scheme_cache: &'a mut HashMap<DefId, Option<typed_ir::Scheme>>,
        base_bounds_cache: &'a mut HashMap<TypeVar, typed_ir::TypeBounds>,
        complete_principal_cache: &'a mut CompletePrincipalCache,
        profile: Option<&'a mut ExprExportProfile>,
        relevant_vars: BTreeSet<typed_ir::TypeVar>,
        edge_evidence: &'a HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
    ) -> Self {
        Self {
            state,
            globals,
            locals: HashMap::new(),
            principal_scheme_cache,
            base_bounds_cache,
            complete_principal_cache,
            principal_callee_scheme_cache: HashMap::new(),
            relevant_bounds_cache: HashMap::new(),
            profile,
            relevant_vars,
            edge_evidence,
            prefer_same_path_effect_ops: 0,
        }
    }
    // ... 1200+ lines using these caches
```

メンバの `locals`、`principal_callee_scheme_cache`、`relevant_bounds_cache` は関数ごとにクリアされない。キャッシュの寿命が明確でない。

**所感**: キャッシュ戦略が分散している。一元化したほうがデバッグしやすいかも。

---

## 6. CompletePrincipalCache と CompletePrincipalStepProfile の不統一なプロファイリング

- **場所**: `crates/yulang-infer/src/export/complete_principal.rs:47-65, 251-320`
- **匂い**: 同じ concept の timing data を 2 つの別な struct で管理

```rust
pub(crate) struct CompletePrincipalCache {
    pub(crate) monomorphic_types: HashMap<TypeVar, Option<typed_ir::Type>>,
    pub(crate) apply_evidence: HashMap<(TypeVar, TypeVar), typed_ir::ApplyEvidence>,
}

pub(crate) struct CompletePrincipalStepProfile {
    pub duration: Duration,
    pub substitution_slots: Duration,
    pub substitution_export: Duration,
    pub substitution_roles: Duration,
    pub substitution_emit: Duration,
    pub(crate) candidates: Duration,
}

pub(super) fn complete_apply_principal_evidence_from_slot_bounds_cached_profiled(
    infer: &Infer,
    requirements: &[typed_ir::RoleRequirement],
    param: &typed_ir::Type,
    ret: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    base_bounds_cache: Option<&mut HashMap<TypeVar, typed_ir::TypeBounds>>,
    cache: &mut CompletePrincipalCache,
    profile: Option<&mut CompletePrincipalStepProfile>,
) -> typed_ir::ApplyEvidence {
    let t = CompletePrincipalClock::now(profile.is_some());
    let evidence = complete_apply_principal_evidence_from_slot_bounds_cached(
        infer, requirements, param, ret, params, arg_tv, result_tv, slot_bounds,
        base_bounds_cache, cache,
    );
    if let Some(profile) = profile.as_deref_mut() {
        profile.duration += t.elapsed();
    }
    evidence
}
```

profile が optional で、毎回 `profile.is_some()` チェックを書く。ExprExportProfile のようなより詳細な profile struct と共存している。

**所感**: profile の構造を統一してもいいかも。

---

## 7. PrincipalSubstitutionUnifier の複雑な bind 戦略

- **場所**: `crates/yulang-infer/src/export/complete_principal.rs:2190-2212`
- **匂い**: 型の unification がハード、特に conflict と binding の関係

```rust
    fn bind(&mut self, var: &typed_ir::TypeVar, actual: &typed_ir::Type, allow_never: bool) {
        if !substitution_type_usable(actual, allow_never) {
            return;
        }
        if self.conflicts.contains(var) {
            return;
        }
        match self.substitutions.get(var) {
            Some(existing) if existing == actual => {}
            Some(existing) => {
                if let Some(merged) = merge_substitution_type(existing, actual) {
                    self.substitutions.insert(var.clone(), merged);
                } else {
                    self.substitutions.remove(var);
                    self.conflicts.insert(var.clone());
                }
            }
            None => {
                self.substitutions.insert(var.clone(), actual.clone());
            }
        }
    }
```

conflict state を記録するが、infer() メソッドからはこの constraints が見えない。バインディング戦略が不明瞭。

**所感**: conflict の理由をもっと明確にしてもいいかも。

---

## 8. type_bounds_* と value_type_bounds_* の重複判定関数群

- **場所**: `crates/yulang-infer/src/export/complete_principal.rs:2319-2530` (multiple functions)
- **匂い**: Boolean-blind type judgment 関数が 10+ 個存在

```rust
fn type_fits_bounds(ty: &typed_ir::Type, bounds: &typed_ir::TypeBounds) -> bool { ... }
fn type_has_vars(ty: &typed_ir::Type) -> bool { ... }
fn substitution_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool { ... }
fn type_has_unknown(ty: &typed_ir::Type) -> bool { ... }
fn type_bounds_closed(bounds: &typed_ir::TypeBounds) -> bool { ... }
fn type_bounds_informative(bounds: &typed_ir::TypeBounds) -> bool { ... }
fn value_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool { ... }
fn effect_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool { ... }
fn type_arg_has_unknown(arg: &typed_ir::TypeArg) -> bool { ... }
fn type_arg_runtime_usable(arg: &typed_ir::TypeArg) -> bool { ... }
fn primary_structural_or_concrete_type(ty: &typed_ir::Type) -> Option<&typed_ir::Type> { ... }
```

各関数が 1-20 行で、true/false/Option を返すだけ。これらをまとめた trait や enum を使うと maintainability が上がるかも。

**所感**: これだけ判定関数があると、それぞれの前提条件を把握しづらい。ドメイン言語を作ってもいいかも。

---

## 9. export_core_program の 171 行 timing instrumentation 混在

- **場所**: `crates/yulang-infer/src/export/principal.rs:61-231`
- **匂い**: business logic とタイミング計測の混在、5 段階の clock instances

```rust
pub fn export_core_program(state: &mut LowerState) -> typed_ir::CoreProgram {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let t0 = ExportClock::now(export_timing);
    let t_setup_refresh_before = ExportClock::now(export_timing);
    state.refresh_selection_environment();
    if export_timing {
        eprintln!(
            "  export: setup.refresh_before={:.3}ms",
            t_setup_refresh_before.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t_binding_paths = ExportClock::now(export_timing);
    let binding_paths = state.ctx.collect_all_binding_paths();
    if export_timing {
        eprintln!(
            "  export: setup.binding_paths={:.3}ms count={}",
            t_binding_paths.elapsed().as_secs_f64() * 1000.0,
            binding_paths.len()
        );
    }
    // ... 11 more timing blocks ...
    let t1 = ExportClock::now(export_timing);
    let expected_edge_evidence = collect_expected_edge_evidence(state);
    if export_timing {
        eprintln!(
            "  export: collect_edge_evidence={:.3}ms edges={}",
            t1.elapsed().as_secs_f64() * 1000.0,
            expected_edge_evidence.len()
        );
    }
    // ... more work ...
}
```

計測コードが 60+ 行を占める。AspectOrientedProgramming 風の decorator があるといいかも。

**所感**: 計測機能を分離してもいいかも。

---

## 10. export_bindings_for_paths の 19 行の eprintln! dump

- **場所**: `crates/yulang-infer/src/export/principal.rs:872-890`
- **匂い**: 非常に長い debug string、複数の `.as_secs_f64() * 1000.0` 繰り返し

```rust
            eprintln!(
                "      exprs={}, applies={}, bounds_misses={}, bounds={:.3}ms, coalesced_apply_bounds={:.3}ms, principal_scheme={:.3}ms (direct={:.3}ms, residual={:.3}ms), principal_evidence={:.3}ms (subs={:.3}ms [slots={:.3}ms, export={:.3}ms, roles={:.3}ms, emit={:.3}ms], candidates={:.3}ms), principal_plan={:.3}ms",
                profile.exprs,
                profile.applies,
                profile.bounds_misses,
                profile.bounds.as_secs_f64() * 1000.0,
                profile.coalesced_apply_bounds.as_secs_f64() * 1000.0,
                profile.principal_scheme.as_secs_f64() * 1000.0,
                profile.principal_scheme_direct.as_secs_f64() * 1000.0,
                profile.principal_scheme_residual.as_secs_f64() * 1000.0,
                profile.principal_evidence.as_secs_f64() * 1000.0,
                profile.principal_evidence_substitutions.as_secs_f64() * 1000.0,
                profile.principal_evidence_substitution_slots.as_secs_f64() * 1000.0,
                profile.principal_evidence_substitution_export.as_secs_f64() * 1000.0,
                profile.principal_evidence_substitution_roles.as_secs_f64() * 1000.0,
                profile.principal_evidence_substitution_emit.as_secs_f64() * 1000.0,
                profile.principal_evidence_candidates.as_secs_f64() * 1000.0,
                profile.principal_plan.as_secs_f64() * 1000.0,
            );
```

16 個の field が 1 行に詰まっている。ここのコードは paths.rs の complete_referenced_binding_closure にも同じコードが存在。

**所感**: formatting helper を切り出してもいいかも。

---

## 11. expect() call in test with non-trivial precondition

- **場所**: `crates/yulang-infer/src/export/principal.rs:2160`
- **匂い**: expect() の前に複雑な find_map chain

```rust
            .iter()
            .find_map(|binding| find_coerce_evidence(&binding.body, concrete_coerce_evidence))
            .expect("synthetic field projection should carry concrete coerce evidence");
```

この expect() の直前に binding.body の traverse で coerce evidence を探している。binding が複数個あるとき失敗する可能性。test code なので許容されるが、precondition が不透明。

**所感**: test 内での complex assertion。本当に assert 不可能な場所か確認したほうがいいかも。

---

## 12. collect_export_target_defs の mutation-heavy pending stack

- **場所**: `crates/yulang-infer/src/export/principal.rs:1277-1314`
- **匂い**: while loop + mutation + pending push/pop の不明瞭な不変量

```rust
fn collect_export_target_defs(
    state: &LowerState,
    binding_paths: &[(Path, DefId)],
) -> HashSet<DefId> {
    let mut target_defs = HashSet::new();
    let mut pending = Vec::new();

    for (path, block) in &state.top_level_blocks {
        if !path.segments.is_empty() {
            continue;
        }
        extend_target_defs_from_block(
            state,
            block,
            &exportable_defs,
            &mut target_defs,
            &mut pending,
        );
    }
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    target_defs.extend(collect_hir_role_rewrite_support_defs(state));

    while let Some(def) = pending.pop() {
        let Some(body) = state.principal_bodies.get(&def) else {
            continue;
        };
        extend_target_defs_from_expr(
            state,
            body,
            &exportable_defs,
            &mut target_defs,
            &mut pending,
        );
    }

    target_defs
}
```

pending ベクタの insert/pop の順番（DFS vs BFS）が呼び出し元で制御されている。extend_* 関数側で pending を push することで、invariant が分散。

**所感**: 深さ優先・幅優先のどちらが想定か不明。もっと explicit にするといいかも。

