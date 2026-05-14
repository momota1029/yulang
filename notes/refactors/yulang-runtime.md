# yulang-runtime: Code Smell Report

まるで古い家を改築していくような感じで、yulang-runtime にはおおらかな構造の問題が積み重なっているようですね。主な悪臭は、巨大な単一ファイルと細かすぎる boolean フラグを使った制御フロー、そして似たようなコードが複数存在することあたりでしょうか。個別修正ではなく、モジュール設計の見直しと型駆動設計で改善できそうな部分が多く見られます。

---

## 1. principal_unify.rs: 9000行超の巨大ファイル with 350-400行関数

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
- **匂い**: ファイルが大きすぎる、関数が長すぎる

```rust
// principal_unify.rs 全体が 9039 行
// そのうち単一メソッドが 350+ 行の例：

fn rewrite_apply_from_principal_plan(
    &mut self,
    expr: &Expr,
    result_context: Option<&typed_ir::TypeBounds>,
) -> Option<Expr> {
    self.bump("principal-unify-apply");
    let started = self.profile_timer();
    let Some(spine) = principal_unify_apply_spine(expr) else {
        self.finish_profile_timer("apply-spine", started);
        return None;
    };
    self.finish_profile_timer("apply-spine", started);
    if self.should_skip_partial_callee_rewrite(spine.target, spine.args.len()) {
        return None;
    }
    // ... 374 行もある
}

fn rewrite_expr_inner(
    &mut self,
    expr: Expr,
    result_context: Option<typed_ir::TypeBounds>,
) -> Expr {
    // ... 350 行 ...
    match expr.kind {
        ExprKind::Apply { callee, arg, evidence, instantiation } => {
            // ... complex logic
        }
        // ... many arms
    }
}
```

**所感**: 単一ファイルが 9000 行超は誰も読めません。unification / rewriting / planning の関心ごとを 3-4 個の独立したモジュールに分割するほうがいいかもね。特に `rewrite_expr_inner` は state 機械に見えるのに method のままというのが怪しい。

---

## 2. substitution.rs: Boolean-blind インターフェース

- **場所**: `crates/yulang-runtime/src/types/substitution.rs:1-55`
- **匂い**: Boolean flag パラメータ

```rust
pub(crate) fn infer_type_substitutions(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        128,      // <- depth (magic number!)
        false,    // <- include_function_effects
        false,    // <- prefer_non_never
        false,    // <- skip_empty_effect_residual
    );
}

pub(crate) fn infer_type_substitutions_prefer_non_never(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        128,
        false,
        true,     // <- only this changed
        false,
    );
}

pub(crate) fn infer_type_substitutions_prefer_non_never_skip_empty_effects(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(
        template,
        actual,
        params,
        substitutions,
        128,
        false,
        true,
        true,     // <- and this one
    );
}
```

**所感**: これ `InferenceOptions` struct で表したら、関数が複数ある方が分かりやすいと思いませんか。フラグの組み合わせ (false,false,false), (false,true,false), (false,true,true) のようなシーケンスは保守が大変〜

---

## 3. handler_boundary.rs: 双子関数 `remove_consumed_effects` と `select_consumed_effects`

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/handler_boundary.rs:470-540`
- **匂い**: ほぼ同一コード、引数で動作が変わる

```rust
fn remove_consumed_effects(effect: &typed_ir::Type, consumed: &[typed_ir::Path]) -> typed_ir::Type {
    match effect {
        typed_ir::Type::Named { path, .. }
            if consumed.iter().any(|consumed| effect_paths_match(consumed, path)) =>
        {
            typed_ir::Type::Never  // <- Remove case
        }
        typed_ir::Type::Row { items, tail } => {
            let items = items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))  // <- Recursive
                .filter(|item| !effect_is_empty(item))
                .collect();
            let tail = remove_consumed_effects(tail, consumed);
            effect_row(items, tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => effect_row(
            items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect(),
            typed_ir::Type::Never,
        ),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(remove_consumed_effects(body, consumed)),
        },
        other => other.clone(),
    }
}

fn select_consumed_effects(effect: &typed_ir::Type, consumed: &[typed_ir::Path]) -> typed_ir::Type {
    match effect {
        typed_ir::Type::Named { path, .. }
            if consumed.iter().any(|consumed| effect_paths_match(consumed, path)) =>
        {
            effect.clone()  // <- Select case (mirror of above!)
        }
        typed_ir::Type::Row { items, tail } => {
            let items = items
                .iter()
                .map(|item| select_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect();
            let tail = select_consumed_effects(tail, consumed);
            effect_row(items, tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => effect_row(
            items
                .iter()
                .map(|item| select_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect(),
            typed_ir::Type::Never,
        ),
        // ... same recursive case
        other => other.clone(),
    }
}
```

**所感**: enum `EffectFilterMode { Keep, Remove }` みたいなのを作って、ジェネリック fold を 1 つ書くほうがメンテ楽かも。今のコードは同期ズレのバグの温床〜

---

## 4. monomorphize/mod.rs: 1800行超の mod.rs で構成図不明

- **場所**: `crates/yulang-runtime/src/monomorphize/mod.rs:1-100`
- **匂い**: mod.rs が大きすぎる

```rust
// mod.rs が全体で 1853 行
// submodule が多いが mod.rs 自体も substantial

//! Monomorphization and specialization.
//! The default path is principal-elaboration based...
//! The legacy demand-driven fixpoint path is retained...

mod associated;
mod check;
mod collect;
mod demand_profile;
mod demand_queue;
mod emit;
mod engine;
mod pipeline;
mod semantics;
mod solve;
mod specialize;

// そして mod.rs 自体に DemandKey, Demand, DemandSemantics などの大きな構造が
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Demand {
    pub target: typed_ir::Path,
    pub expected: RuntimeType,
    pub key: DemandKey,
}

// ... 大量の impl ブロック ...
```

**所感**: `mod.rs` が façade と実装を混ぜてる印象。`demand.rs`, `semantics_re_export.rs` みたいなの作ってモジュール境界を明確にしたら分かりやすくなるんじゃないかな〜

---

## 5. emit.rs: 5000行超、「collect and rewrite」が融合

- **場所**: `crates/yulang-runtime/src/monomorphize/emit.rs`
- **匂い**: 2つの責務が混在

```rust
// emit.rs は実装が 5041 行
pub struct DemandEmitter<'a> {
    semantics: DemandSemantics,
    bindings: HashMap<typed_ir::Path, &'a Binding>,
    pure_handler_bindings: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    ordered_specializations: &'a [DemandSpecialization],
    specializations: HashMap<DemandKey, &'a DemandSpecialization>,
    checked: HashMap<DemandKey, &'a CheckedDemand>,
}

// ... rewrite_expr, rewrite_lambda, insert_checked_pattern_bindings
//     collect_expr_thunk_effects, merge_optional_handler_effect
//     これら別の概念を全部やってる
```

**所感**: demand specialization の emit と expr の rewrite は分離のほうが読みやすいと思うんですけど。例えば `DemandEmitStrategy` trait を作って、`RewriteStrategy` と `CollectStrategy` に分けるとか〜

---

## 6. check.rs: 5300行、ExprChecker の責務が大きすぎる

- **場所**: `crates/yulang-runtime/src/monomorphize/check.rs`
- **匂い**: 単一構造体で多すぎる責務

```rust
pub struct DemandChecker<'a> {
    semantics: DemandSemantics,
    bindings: HashMap<typed_ir::Path, &'a Binding>,
    generic_bindings: HashSet<typed_ir::Path>,
    generic_role_impls: HashMap<typed_ir::Name, Vec<RoleImplDemandCandidate>>,
    pure_handler_bindings: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
}

// check_expr は ExprKind の全パターン + generic_arg_signature 判定 + role_impl 検索...
// これぐらいなら 5300 行になってもおかしくない
```

**所感**: ExprChecker の中で check と search が混在してるみたい。`ExprTypeChecker`, `RoleImplFinder` みたいな専門クラスに分割するほうが単体テストも書きやすいんじゃないかな〜

---

## 7. lowerer.rs: 2800行、引数を 4-5個取る大型メソッド

- **場所**: `crates/yulang-runtime/src/lower/lowerer.rs:76-82`
- **匂い**: 多くの引数、複雑な型変換

```rust
pub(super) fn lower_expr(
    &mut self,
    expr: typed_ir::Expr,
    expected: Option<&RuntimeType>,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    expected_source: TypeSource,
) -> RuntimeResult<Expr> {
    // ... huge match
}

pub(super) fn lower_binding(
    &mut self,
    binding: typed_ir::PrincipalBinding,
) -> RuntimeResult<Binding> {
    let body_is_constructor_variant = is_constructor_variant_expr(&binding.body);
    let old_binding = self.current_binding.replace(binding.name.clone());
    let body_ty = self.binding_runtime_type(&binding);
    let alias_runtime_ty = self.alias_target_runtime_type(&binding);
    // ... 60+ lines of setup before actually lowering
}
```

**所感**: Lowerer が state 管理しながら contextual computation やってるパターン。引数の `expected` と `locals` は state に持たせるのはどうでしょう。今は一時的には効果あるけど、長期的には記述量が増えそう〜

---

## 8. principal_unify.rs: ProfileTimer と bump/recording が散らばっている

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs:314-495`
- **匂い**: Profiling code が本体に混在

```rust
fn rewrite_apply_from_principal_plan(
    &mut self,
    expr: &Expr,
    result_context: Option<&typed_ir::TypeBounds>,
) -> Option<Expr> {
    self.bump("principal-unify-apply");         // <- profiling
    let started = self.profile_timer();         // <- profiling
    let Some(spine) = principal_unify_apply_spine(expr) else {
        self.finish_profile_timer("apply-spine", started);  // <- profiling
        return None;
    };
    self.finish_profile_timer("apply-spine", started);     // <- profiling
    // ... business logic ...
    self.bump("principal-unify-runtime-effect-skip-adapter");  // <- profiling
    self.record_target_apply_visit(spine.target);              // <- profiling
    // ...
}

// メソッド群：
fn bump(&mut self, key: &'static str) { self.stats.entry(key).and_modify(...) }
fn add_timing(&mut self, key: &'static str, duration: Duration) { ... }
fn profile_timer(&self) -> Option<Instant> { ... }
fn finish_profile_timer(&mut self, key: &'static str, started: Option<Instant>) { ... }
fn record_target_apply_visit(&mut self, target: &typed_ir::Path) { ... }
fn record_target_rewrite(&mut self, target: &typed_ir::Path) { ... }
```

**所感**: Profiling のための field が 5 個以上あって、メソッドも 10+ 個。これ `ProfileCollector` という companion struct に抜き出して、decoratorパターンで wrap するほうがキレイじゃないかな〜。今のままだと profiling を disable したくても無理。

---

## 9. handler_boundary.rs: 複数の `effect_` 操作関数が細かく分かれている

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/handler_boundary.rs:392-540`
- **匂い**: 再帰的効果操作が複数ファイルに分散

```rust
fn merge_effects(left: Option<typed_ir::Type>, right: Option<typed_ir::Type>) -> Option<typed_ir::Type> { ... }
fn merge_effect_rows(left: typed_ir::Type, right: typed_ir::Type) -> typed_ir::Type { ... }
fn merge_effect_tails(left: typed_ir::Type, right: typed_ir::Type) -> typed_ir::Type { ... }
fn effect_row_parts(effect: typed_ir::Type) -> (Vec<typed_ir::Type>, typed_ir::Type) { ... }
fn effect_row(items: Vec<typed_ir::Type>, tail: typed_ir::Type) -> typed_ir::Type { ... }
fn push_unique_effect_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) { ... }

// そして remove_consumed_effects, select_consumed_effects (duplicates!)
// そして normalize_effect, effect_contains_unknown_or_var, ...
```

**所感**: Effect manipulation は unified algebra が必要では。Monoid / Lattice structure を反映した trait / trait object の設計で、merge, filter, normalize などを統一的に定義したら、code volume も減りそう〜

---

## 10. collect.rs: Legacy binding tracking with many flags

- **場所**: `crates/yulang-runtime/src/monomorphize/collect.rs`
- **匂い**: Legacy code 用の名前付けと条件分岐

```rust
// collect.rs contains:
// - seed_existing_legacy_specializations()
// - collector_scans_materialized_legacy_body_even_when_type_is_open (test)
// - collector_ignores_unreachable_materialized_legacy_body (test)
// - is_legacy_mono_binding()

// emit.rs では:
// - emitter_rewrites_legacy_mono_call_to_demand_specialization
// - emitter_rewrites_calls_inside_closed_legacy_mono_binding
// - emitter_leaves_legacy_mono_binding_when_rewrite_has_unresolved_holes
// - is_recoverable_legacy_rewrite_error()

// pipeline/mod.rs では:
// - run_legacy_demand_fixpoint_pipeline()
```

**所感**: Legacy code path 全体を 1 つのモジュール `legacy_pipeline.rs` に隔離して、feature flag でコンパイル除外するっていうのはどう？今は mainline code に legacy handling が散在してて読みにくい〜

---

## 11. principal_unify.rs: 複数の specialized signature struct が深く入れ子

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs:22-100`
- **匂い**: State machine for specialization が struct field で表現

```rust
struct PrincipalUnifier {
    // Core state:
    module: Module,
    bindings_by_path: HashMap<typed_ir::Path, Binding>,
    generic_bindings: HashSet<typed_ir::Path>,
    
    // Specialization tracking (3 structs × 複数field):
    pending_specializations: VecDeque<PendingPrincipalSpecialization>,
    active_specializations: Vec<ActivePrincipalSpecialization>,
    specializations: HashMap<String, typed_ir::Path>,
    root_specializations: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    
    // Rewrite context tracking:
    rewrite_contexts: Vec<&'static str>,
    local_use_contexts: Vec<LocalUseContextScope>,
    local_value_contexts: Vec<BTreeMap<typed_ir::Name, RuntimeType>>,
    
    // Caching:
    incomplete_plan_cache: HashMap<IncompletePrincipalPlanKey, CachedIncompletePrincipalPlan>,
    incomplete_plan_targets: HashSet<typed_ir::Path>,
    
    // Profiling (5+ fields):
    stats: HashMap<&'static str, usize>,
    timings: HashMap<&'static str, Duration>,
    target_skips: HashMap<typed_ir::Path, HashMap<&'static str, usize>>,
    target_missing_vars: HashMap<typed_ir::Path, HashMap<typed_ir::TypeVar, usize>>,
    // ...
}
```

**所感**: PrincipalUnifier って state machine なんだけど、state field が 20+ ある。ワークフロー `pending -> active -> emitted` みたいな state を明示的に enum で表して、状態ごとに許される操作を限定するほうが型安全なんじゃないかな〜

---

## 12. Widespread `expect()` / `unwrap()` on non-trivial paths

- **場所**: `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs:3678, 3686, 5406, 8440, 8926, 8945, 8966, 9002`
- **匂い**: Panic-on-error pattern without context

```rust
// Line 3678
let last = matches.pop().expect("non-empty contextual matches");

// Line 8926
let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");
let adapted = principal_arg_adapter(&arg, &bool_ty, &typed_ir::Type::Any).expect("adapter");
let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");
let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

// Line 5406
items.pop().unwrap()
```

**所感**: Precondition がコメントで書かれてるだけで、code path では enforce されてない。`require_non_empty(matches)` とか `let adapted = principal_arg_adapter(...).ok_or(UnifyError::MissingAdapter)?` のように結果型で扱うほうが robust ですかね。

---

## 13. Repeated recursive traversals in emit.rs

- **場所**: `crates/yulang-runtime/src/monomorphize/emit.rs:1700-1850`
- **匂い**: Match statement で ExprKind の全パターンを何度も書く

```rust
// Large match in rewrite_expr で各 ExprKind を処理:
fn rewrite_expr(&mut self, expr: &Expr, expected: Option<&DemandSignature>) -> Result<Expr, DemandEmitError> {
    let mut ty = expr.ty.clone();
    let rewritten = match &expr.kind {
        ExprKind::Apply { callee, arg, evidence, instantiation } => { ... }
        ExprKind::Lambda { param, param_effect_annotation, body } => { ... }
        ExprKind::If { cond, then_branch, else_branch, effect_annotation } => { ... }
        ExprKind::Tuple(items) => { ... }
        ExprKind::Record { fields, spread } => { ... }
        // ... 20+ arms ...
    };
    // ...
}

// そしてほぼ同じ match pattern が別の関数 check_expr でも:
fn check_expr(&self, expr: &Expr, expected: &DemandSignature) -> Result<DemandSignature, DemandCheckError> {
    match &expr.kind {
        ExprKind::Apply { ... } => { ... }
        ExprKind::Lambda { ... } => { ... }
        // ... 同じパターン 20+ ...
    }
}
```

**所感**: ExprKind visitor pattern を trait ベースの design で共通化したら、new variant 追加の時に全部のメソッドで対応する必要がなくなると思うんですけど〜

---

## 14. Semantic duplication: _prefer_non_never variants

- **場所**: `crates/yulang-runtime/src/types/substitution.rs` 全体
- **匂い**: 同じロジックで flag による分岐

```rust
pub(crate) fn infer_type_substitutions(...)
pub(crate) fn infer_type_substitutions_prefer_non_never(...)
pub(crate) fn infer_type_substitutions_prefer_non_never_skip_empty_effects(...)

// 全部が同じ internal function を呼ぶだけで、booleans で制御
infer_type_substitutions_inner(
    template, actual, params, substitutions,
    128, false, false, false  // または true, true など
);
```

**所感**: これ builder pattern で `InferenceBuilder::new().prefer_non_never(true).skip_empty_effects(true).run()` みたいに write したら、expand しやすくなるんじゃないかな〜。それか enum `InferenceStrategy { Default, PreferNonNever, PreferNonNeverSkipEmpty }` で型安全に〜

---

## Summary

yulang-runtime の主な悪臭は：

1. **巨大ファイル+長関数**: principal_unify.rs (9000行), check.rs (5300行), emit.rs (5000行) をまず module 単位で分割する必要がある。
2. **Boolean-blind design**: substitution.rs の flag cascade, emit.rs の strategy 選択が enum / strategy trait で表現できていない。
3. **Semantic duplication**: handler_boundary.rs の remove/select, emit.rs の複数 match patterns, collect/check の legacy handling。抽象化のチャンスが多い。
4. **State explosion**: PrincipalUnifier, DemandEmitter などが 20+ field を持ってる。state machine を enum で表現したら invariant が型で守られる。
5. **Profiling cross-cutting**: principal_unify.rs の stats/timing/profiling が business logic に混在。decorator / companion pattern で分離する余地がある。
6. **Legacy code**: 3+ ファイルに legacy mono path が散らばってる。隔離がおすすめ。

これら は incremental に refactor できるんですけど、型駆動設計 (enum, trait) への改造が根底にある気がします。特に substitution と monomorphize/pipeline あたりから始めるといいかも。

