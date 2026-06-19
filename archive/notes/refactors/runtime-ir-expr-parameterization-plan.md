# Refactor: Parameterize `runtime_ir` over type stage & eliminate `restore_*`

**Status**: Spec (drafted 2026-05-25, ready for execution by Codex).
**Audience**: An engineer (or Codex) who has not been in the prior design discussion.
**Scope**: `crates/yulang-runtime-ir`, `crates/yulang-runtime-finalize`, `crates/yulang-runtime`. The CLI driver (`crates/yulang/src/main.rs`) needs a tiny path change.

---

## 1. Motivation

### 1.1 The smell

`yulang_runtime_ir::Type` currently mixes two different "stages" of type information into one enum:

```rust
pub enum Type {
    Unknown,
    Core(typed_ir::Type),       // ← pre-finalize: infer-time type as-is
    Fun { param, ret },          // ← post-finalize: VM-shaped function
    Thunk { effect, value },     // ← post-finalize: explicit thunk wrap
}
```

The `Core(typed_ir::Type)` variant is the half-converted state: we kept the infer-time type around because finalize hadn't yet decided where Thunk boundaries belong.

Because of this, finalize ends up doing the following dance:

1. Materialize a `RuntimeType` by substituting type variables;
2. Notice that the materialized form has lost the effect information that was encoded in the principal's Thunk wrappers (because `RuntimeType::Fun { param, ret }` has no effect fields);
3. Run a post-pass (`restore_runtime_effect_boundaries`, `restore_apply_spine_arg_effects`, `restore_apply_arg_effect`) that walks the materialized form *and the principal in lockstep* and re-injects Thunks where they got lost.

The `restore_*` pass exists only because the intermediate state is lossy. If we never produce a lossy intermediate, the pass is unnecessary.

### 1.2 The fix in one sentence

Split `runtime_ir::Type` into two distinct stages and parameterize the IR over which stage it carries.

- **Pre-finalize stage**: `expr.ty` is just `typed_ir::Type`. Effect information is fully present (`typed_ir::Type::Fun` already has `param_effect` and `ret_effect`).
- **Post-finalize stage**: `expr.ty` is a new `FinalizedType` enum, which is the VM-shaped form (Fun + Thunk wrappers, no raw infer type variables).

The two stages share the same expression tree shape but differ only in the type carried at each node. We express this with a generic parameter `T`:

```rust
pub struct Expr<T> {
    pub ty: T,
    pub kind: ExprKind<T>,
}
```

Then:

- `type LoweredExpr = Expr<yulang_typed_ir::Type>;`
- `type FinalizedExpr = Expr<FinalizedType>;`

Finalize becomes a function `LoweredExpr → FinalizedExpr` (lifted to module level). Inside finalize, every position is statically known to be one stage or the other; no lossy intermediate exists; `restore_*` is deleted.

---

## 2. Target shape

### 2.1 `runtime_ir::FinalizedType`

```rust
/// Post-finalize "VM-shaped" type. Fun never carries effect directly;
/// effected positions are wrapped in `Thunk`. The `Value` variant holds
/// any non-function infer type (int, record, tuple, variant, etc.).
///
/// Invariant (enforced by construction, not by the type system):
///   `FinalizedType::Value(t)` never has `t == typed_ir::Type::Fun { .. }`.
///   Function types always appear as `FinalizedType::Fun { .. }`.
#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FinalizedType {
    Unknown,
    Value(yulang_typed_ir::Type),
    Fun {
        param: Box<FinalizedType>,
        ret: Box<FinalizedType>,
    },
    Thunk {
        effect: yulang_typed_ir::Type,
        value: Box<FinalizedType>,
    },
}
```

Keep the existing non-recursive `Clone` impl pattern (mirror of `clone_type_without_fun_spine_recursion`). Deep Fun/Thunk spines are common — recursive Clone may overflow the stack.

Convenience constructors (mirror existing `Type::core` / `Type::fun` / `Type::thunk` / `Type::unknown`):

```rust
impl FinalizedType {
    pub fn unknown() -> Self { Self::Unknown }
    pub fn value(ty: yulang_typed_ir::Type) -> Self {
        debug_assert!(!matches!(ty, yulang_typed_ir::Type::Fun { .. }),
            "FinalizedType::Value must not wrap Fun; use FinalizedType::Fun instead");
        Self::Value(ty)
    }
    pub fn fun(param: FinalizedType, ret: FinalizedType) -> Self {
        Self::Fun { param: Box::new(param), ret: Box::new(ret) }
    }
    pub fn thunk(effect: yulang_typed_ir::Type, value: FinalizedType) -> Self {
        Self::Thunk { effect, value: Box::new(value) }
    }
}
```

Provide `From<yulang_typed_ir::Type> for FinalizedType` only if it can enforce the invariant (recursively walk and lift `Fun` into `FinalizedType::Fun`). See §4.3 for the conversion function `finalized_from_typed_ir`.

### 2.2 Parameterize the IR

Add a type parameter `T` to every struct/enum in `runtime_ir/src/lib.rs` that currently carries a `Type` field. The parameter represents "what type is in each `.ty` slot."

```rust
pub struct Expr<T> {
    pub ty: T,
    pub kind: ExprKind<T>,
}

pub enum ExprKind<T> {
    Var(typed_ir::Path),
    EffectOp(typed_ir::Path),
    PrimitiveOp(typed_ir::PrimitiveOp),
    Lit(typed_ir::Lit),
    Lambda {
        param: typed_ir::Name,
        param_effect_annotation: Option<typed_ir::ParamEffectAnnotation>,
        param_function_allowed_effects: Option<typed_ir::FunctionSigAllowedEffects>,
        body: Box<Expr<T>>,
    },
    Apply {
        callee: Box<Expr<T>>,
        arg: Box<Expr<T>>,
        evidence: Option<typed_ir::ApplyEvidence>,
        instantiation: Option<TypeInstantiation>,
    },
    If {
        cond: Box<Expr<T>>,
        then_branch: Box<Expr<T>>,
        else_branch: Box<Expr<T>>,
        evidence: Option<JoinEvidence>,
    },
    Tuple(Vec<Expr<T>>),
    Record {
        fields: Vec<RecordExprField<T>>,
        spread: Option<RecordSpreadExpr<T>>,
    },
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<Expr<T>>>,
    },
    Select {
        base: Box<Expr<T>>,
        field: typed_ir::Name,
    },
    Match {
        scrutinee: Box<Expr<T>>,
        arms: Vec<MatchArm<T>>,
        evidence: JoinEvidence,
    },
    Block {
        stmts: Vec<Stmt<T>>,
        tail: Option<Box<Expr<T>>>,
    },
    Handle {
        body: Box<Expr<T>>,
        arms: Vec<HandleArm<T>>,
        evidence: JoinEvidence,
        handler: HandleEffect,
    },
    BindHere {
        expr: Box<Expr<T>>,
    },
    Thunk {
        effect: typed_ir::Type,
        value: T,                 // ← was `Type`; now `T`
        expr: Box<Expr<T>>,
    },
    LocalPushId { id: EffectIdVar, body: Box<Expr<T>> },
    PeekId,
    FindId { id: EffectIdRef },
    AddId {
        id: EffectIdRef,
        allowed: typed_ir::Type,
        active: bool,
        thunk: Box<Expr<T>>,
    },
    Coerce {
        from: typed_ir::Type,
        to: typed_ir::Type,
        expr: Box<Expr<T>>,
    },
    Pack {
        var: typed_ir::TypeVar,
        expr: Box<Expr<T>>,
    },
}
```

Also parameterize:

```rust
pub struct Module<T> {
    pub path: typed_ir::Path,
    pub bindings: Vec<Binding<T>>,
    pub root_exprs: Vec<Expr<T>>,
    pub roots: Vec<Root>,
    pub role_impls: Vec<typed_ir::RoleImplGraphNode>,
}

pub struct Binding<T> {
    pub name: typed_ir::Path,
    pub type_params: Vec<typed_ir::TypeVar>,
    pub scheme: typed_ir::Scheme,
    pub body: Expr<T>,
}

pub enum Stmt<T> {
    Let { pattern: Pattern<T>, value: Expr<T> },
    Expr(Expr<T>),
    Module { def: typed_ir::Path, body: Expr<T> },
}

pub enum Pattern<T> {
    Wildcard { ty: T },
    Bind { name: typed_ir::Name, ty: T },
    Lit { lit: typed_ir::Lit, ty: T },
    Tuple { items: Vec<Pattern<T>>, ty: T },
    List {
        prefix: Vec<Pattern<T>>,
        spread: Option<Box<Pattern<T>>>,
        suffix: Vec<Pattern<T>>,
        ty: T,
    },
    Record {
        fields: Vec<RecordPatternField<T>>,
        spread: Option<RecordSpreadPattern<T>>,
        ty: T,
    },
    Variant { tag: typed_ir::Name, value: Option<Box<Pattern<T>>>, ty: T },
    Or { left: Box<Pattern<T>>, right: Box<Pattern<T>>, ty: T },
    As { pattern: Box<Pattern<T>>, name: typed_ir::Name, ty: T },
}

pub struct RecordExprField<T> { pub name: typed_ir::Name, pub value: Expr<T> }
pub enum RecordSpreadExpr<T> { Head(Box<Expr<T>>), Tail(Box<Expr<T>>) }
pub struct RecordPatternField<T> { pub name: typed_ir::Name, pub pattern: Pattern<T>, pub default: Option<Expr<T>> }
pub enum RecordSpreadPattern<T> { Head(Box<Pattern<T>>), Tail(Box<Pattern<T>>) }
pub struct MatchArm<T> { pub pattern: Pattern<T>, pub guard: Option<Expr<T>>, pub body: Expr<T> }
pub struct HandleArm<T> { pub effect: typed_ir::Path, pub payload: Pattern<T>, pub resume: Option<ResumeBinding<T>>, pub guard: Option<Expr<T>>, pub body: Expr<T> }
pub struct ResumeBinding<T> { pub name: typed_ir::Name, pub ty: T }
```

Items that **do not** need parameterization (no `Type` field, only typed_ir entities):

- `JoinEvidence` (just `result: typed_ir::Type`)
- `HandleEffect` (paths + typed_ir types only)
- `TypeInstantiation`, `TypeSubstitution`
- `EffectIdVar`, `EffectIdRef`
- `Root`

### 2.3 Type aliases

Expose two convenience aliases at the crate root:

```rust
pub type LoweredExpr        = Expr<yulang_typed_ir::Type>;
pub type LoweredExprKind    = ExprKind<yulang_typed_ir::Type>;
pub type LoweredModule      = Module<yulang_typed_ir::Type>;
pub type LoweredBinding     = Binding<yulang_typed_ir::Type>;
pub type LoweredStmt        = Stmt<yulang_typed_ir::Type>;
pub type LoweredPattern     = Pattern<yulang_typed_ir::Type>;
pub type LoweredMatchArm    = MatchArm<yulang_typed_ir::Type>;
pub type LoweredHandleArm   = HandleArm<yulang_typed_ir::Type>;
// ... etc for every parameterized struct/enum

pub type FinalizedExpr      = Expr<FinalizedType>;
pub type FinalizedExprKind  = ExprKind<FinalizedType>;
pub type FinalizedModule    = Module<FinalizedType>;
pub type FinalizedBinding   = Binding<FinalizedType>;
pub type FinalizedStmt      = Stmt<FinalizedType>;
pub type FinalizedPattern   = Pattern<FinalizedType>;
// ... etc
```

Downstream code uses the alias at use sites:

```rust
use yulang_runtime_ir::{FinalizedExpr, FinalizedModule};
```

### 2.4 `walk.rs` becomes generic

Every walker in `crates/yulang-runtime-ir/src/walk.rs` gains a `<T>` parameter:

```rust
pub fn walk_children<T, F: FnMut(&Expr<T>)>(expr: &Expr<T>, mut f: F) {
    walk_children_impl(expr, &mut f);
}

fn walk_children_impl<T, F: FnMut(&Expr<T>)>(expr: &Expr<T>, f: &mut F) { /* ... */ }

pub fn walk_children_any<T, F: FnMut(&Expr<T>) -> bool>(expr: &Expr<T>, mut f: F) -> bool { /* ... */ }

pub fn walk_children_mut<T, F: FnMut(&mut Expr<T>)>(expr: &mut Expr<T>, mut f: F) { /* ... */ }

pub fn walk_children_try_mut<T, E, F: FnMut(&mut Expr<T>) -> Result<(), E>>(
    expr: &mut Expr<T>, mut f: F,
) -> Result<(), E> { /* ... */ }

pub fn walk_stmt_exprs<T, F: FnMut(&Expr<T>)>(stmt: &Stmt<T>, mut f: F) { /* ... */ }
pub fn walk_pattern_exprs<T, F: FnMut(&Expr<T>)>(pattern: &Pattern<T>, mut f: F) { /* ... */ }
```

No body change is needed beyond threading `T`. The match arms over `ExprKind` already structurally match the new variants since the variants didn't change shape — only `Box<Expr>` became `Box<Expr<T>>`.

### 2.5 Trait derivations

For every parameterized struct/enum, the derives need `T` bounds. Two options:

**Option α (preferred)**: Use bound projection on the derive:

```rust
#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Expr<T> {
    pub ty: T,
    pub kind: ExprKind<T>,
}
```

This works out of the box for `Debug/PartialEq/Eq/Hash/Serialize/Deserialize` — Rust's derive adds `where T: TraitName` automatically (with implicit bound on `T` inside the type).

But `Hash` and `Eq` require `T: Hash` and `T: Eq`. `Serialize`/`Deserialize` (via serde) require `T: Serialize`/`for<'de> T: Deserialize<'de>`. All of these are satisfied by both `typed_ir::Type` and `FinalizedType`, so the derive will work.

**Manual `Clone` for `Expr<T>`**: The existing `Clone for Expr` uses a non-recursive frame stack (`clone_expr_without_apply_spine_recursion`) to avoid stack overflow on deep Apply spines. Generalize this to `Clone for Expr<T> where T: Clone`. The frame stack stores `&'a T` references in place of `&'a Type` references.

**Manual `Clone` for `FinalizedType`**: Mirror the existing `clone_type_without_fun_spine_recursion`, just for `FinalizedType` variants.

### 2.6 Cargo features / dependencies

`yulang-runtime-ir/Cargo.toml`: no new deps. Continue to depend on `yulang-typed-ir`, `serde`.

---

## 3. Migration plan (in execution order)

Each numbered step should leave the workspace in a `cargo check`-able state where possible. Where it cannot (e.g. mid-way through finalize), mark with **breaks compile**.

### Step 1 — Add `FinalizedType` and parameterize IR (runtime-ir only)

1. In `crates/yulang-runtime-ir/src/lib.rs`:
   - Rename the existing enum `Type` → leave it for now as a transitional alias if needed (or delete; see below).
   - Add `FinalizedType` per §2.1.
   - Parameterize all relevant structs/enums per §2.2 with `<T>`.
   - Add type aliases per §2.3.
   - Update the manual `Clone for Expr` to `Clone for Expr<T> where T: Clone`. Generalize the frame stack.
   - Add manual `Clone for FinalizedType` mirroring the existing pattern.

2. In `crates/yulang-runtime-ir/src/walk.rs`:
   - Generic-ify every walker per §2.4.

3. **Decision: delete the old `Type` enum.** With `LoweredType = typed_ir::Type` and `FinalizedType` as the post-finalize form, the old `Type` enum has no callers in the new design. Delete it (and `clone_type_without_fun_spine_recursion`).

4. **Verify**: `cargo check -p yulang-runtime-ir` passes. (Compile checks types and derive consistency, nothing runtime to test in this crate alone.)

### Step 2 — Disconnect VM-side of `yulang-runtime` (keep lowering only)

This step makes Step 3 feasible without touching VM code.

`yulang-runtime` is a multi-purpose crate containing:
- `lower::` — required: produces the LoweredModule that finalize consumes
- `monomorphize::`, `refine::` — superseded by `yulang-runtime-finalize`; not on the active path
- `validate::`, `invariant::` — invariant checks; can be stubbed
- `hygiene::` — display helper; orthogonal

Plan:
1. **Do not remove `yulang-runtime` from the workspace.** Lowering still lives there.
2. Update `lower::` to produce `LoweredModule` (= `Module<typed_ir::Type>`). The lowering currently produces `Module` (= `Module<old_Type>`). The new output uses `typed_ir::Type` directly in every `.ty` slot — which is the most natural thing for a lowering step that just preserves infer info.
3. **Stub out non-lowering modules**: `monomorphize::`, `refine::`, `validate::`, `invariant::`, `hygiene::`. Replace each pub fn body with `unimplemented!("disconnected pending runtime rewrite")` or `Ok(())` for ones that return `Result<(), _>`. Keep the signatures so downstream callers compile.
4. **In `crates/yulang-runtime-finalize/src/solver/mod.rs`**, `validate_monomorphized_output` becomes:
   ```rust
   fn validate_monomorphized_output(_module: &FinalizedModule) -> Result<(), ()> {
       // Disabled pending runtime rewrite. See:
       // archive/notes/refactors/runtime-ir-expr-parameterization-plan.md
       Ok(())
   }
   ```
   Update the return type in the caller to drop the `RuntimeError` mapping.

5. **In `crates/yulang/src/main.rs`**, lower path stays the same (`runtime::lower_core_program(...)`), but the function now returns `LoweredModule`. The next call to `yulang_runtime_finalize::finalize_module(lowered.module)` takes `LoweredModule` (matches new finalize signature).

6. **Verify**: `cargo check -p yulang-runtime` passes. `cargo check -p yulang` passes. (The yulang-runtime tests that exercise monomorphize/refine/validate may fail; they're expected to. Mark them `#[ignore]` if needed.)

### Step 3 — Migrate `yulang-runtime-finalize` (the big one)

This is where the bulk of the work happens. Estimated ~274 destructure sites of `RuntimeType::Fun` to update.

#### 3a. Update the crate's type imports

Every file in `crates/yulang-runtime-finalize/src/` that imported `yulang_runtime_ir::Type as RuntimeType` should now import either:

- `FinalizedExpr`, `FinalizedModule`, `FinalizedType`, etc. — for code that produces/consumes the post-finalize form
- `LoweredExpr`, `LoweredModule`, etc. — for code that consumes the pre-finalize form

Most of finalize is "lowered in → finalized out", so for any function that processes Expr through the pipeline, decide which stage it operates on.

**Naming convention** to ease the change: in code that mixes both stages, use:

```rust
use yulang_runtime_ir::{
    FinalizedExpr, FinalizedExprKind, FinalizedModule, FinalizedType,
    LoweredExpr, LoweredExprKind, LoweredModule,
};
```

Then `FinalizedType` replaces uses of old `RuntimeType` and `FinalizedExpr` replaces uses of old `Expr`.

#### 3b. Convert `Core(x)` → `Value(x)` everywhere (in finalize-only code)

The old `Type::Core(typed_ir::Type)` no longer exists. Every match arm of the form:

```rust
RuntimeType::Core(ty) => { ... }
```

becomes:

```rust
FinalizedType::Value(ty) => { ... }
```

Caveat: there are places where the code matched `Core(typed_ir::Type::Fun { .. })` to detect "a function type that hasn't been split into VM form yet." These cases are now impossible — the invariant says `Value` never wraps a Fun. Delete those branches; add `unreachable!()` if needed.

#### 3c. Update `graph.rs`

`graph.rs` is the heart of finalize's solver and currently uses `Type as RuntimeType` extensively. Major helpers to update:

- `materialize_runtime_type(ty: RuntimeType, ...) -> RuntimeType`:

  Replace with `materialize_finalized_type(ty: FinalizedType, ...) -> FinalizedType` (substitution applied to typed_ir slots inside Value/Fun/Thunk; Fun and Thunk structure preserved).

- `runtime_type_from_core_value(ty: typed_ir::Type) -> RuntimeType`:

  Replace with `finalized_from_typed_ir(ty: typed_ir::Type) -> FinalizedType`. See §4.3.

- `runtime_type_from_core_value_and_effect(value, effect)`:

  Replace with `finalized_with_effect(value: typed_ir::Type, effect: typed_ir::Type) -> FinalizedType` — wraps in Thunk if `should_thunk_effect(&effect)`.

- `should_thunk_effect`, `effect_is_empty`: keep as-is.

- `split_runtime_effected_type` / `RuntimeEffectedType` / `RuntimeEffectRef`: keep, operating on `&FinalizedType`.

#### 3d. Delete `restore_*` functions from `postpass.rs`

The following functions become **unreachable** and should be deleted:

- `restore_runtime_effect_boundaries`
- `runtime_effect_boundary_value_matches`
- `restore_apply_spine_arg_effects`
- `restore_apply_arg_effect`

Their call sites in `apply_spine.rs` (`solved_callee_runtime_type`, `solve_simple_apply`) become:

```rust
// before:
//   let callee_type = solved_callee_runtime_type(binding, &principal, &graph);
//   let callee_type = super::restore_apply_spine_arg_effects(callee_type, &spine.steps, local_types);
// after:
let callee_type = solved_callee_finalized_type(binding, &principal, &graph);
```

`solved_callee_finalized_type` is the renamed and simplified version of `solved_callee_runtime_type`, with the restore step removed:

```rust
fn solved_callee_finalized_type(
    binding: &LoweredBinding,
    principal: &PrincipalInstance,
    graph: &GraphSolution,
) -> FinalizedType {
    // The principal-derived finalized type already has thunks in the right
    // places because finalized_from_typed_ir walks the typed_ir Fun
    // structure and emits FinalizedType::Thunk for every non-empty effect.
    finalized_from_typed_ir(graph.materialize_core(principal.principal_type.clone()))
}
```

The previous code computed both `materialized` and `principal_runtime` and ran restore between them. Now we only compute `principal_runtime` (under the new name `principal_finalized`) because `binding.body.ty` (in `LoweredExpr`) carries `typed_ir::Type` which feeds straight through `finalized_from_typed_ir` and yields the correct Thunk structure without restore.

#### 3e. Update `materialize.rs`

The materialize step now converts `LoweredExpr` (with `typed_ir::Type` in `.ty`) → `FinalizedExpr` (with `FinalizedType` in `.ty`).

```rust
pub(crate) fn materialize_expr(
    expr: LoweredExpr,
    substitutions: &[typed_ir::TypeSubstitution],
) -> FinalizedExpr {
    materialize_expr_with_expected(expr, substitutions, None)
}

pub(crate) fn materialize_expr_with_expected(
    expr: LoweredExpr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&FinalizedType>,
) -> FinalizedExpr {
    // 1. Substitute the .ty (which is typed_ir::Type)
    let materialized_core = materialize_core_type(expr.ty, substitutions);
    // 2. Convert to FinalizedType (auto-thunks Fun positions)
    let ty = finalized_from_typed_ir(materialized_core);
    // 3. Recursively materialize the kind
    let kind = match expr.kind {
        // ... convert each variant from LoweredExprKind to FinalizedExprKind,
        //     materializing children and assigning correct FinalizedType .ty's.
    };
    FinalizedExpr { ty, kind }
}
```

Key change: each variant constructs a `FinalizedExprKind` instead of mutating an `ExprKind`. The function signature changes from `(Expr → Expr)` to `(LoweredExpr → FinalizedExpr)`.

For `ExprKind::Thunk` and any other variants whose `.ty`-bearing fields are typed (e.g. `Thunk { value: Type, ... }` becomes `Thunk { value: FinalizedType, ... }`), construct the new variant with `FinalizedType`-valued fields.

`materialize_thunk_apply_arg`, `materialize_apply_arg`, `materialized_apply_expected_arg`, `materialized_runtime_callee_arg`, etc. all change to operate on `FinalizedType`. The "wrap as Thunk" decision is now made via `finalized_with_effect` (the renamed `runtime_type_from_core_value_and_effect`).

#### 3f. Update `apply_spine.rs`, `cast.rs`, `rewrite.rs`, `role.rs`, `postpass.rs`

These modules currently work on `Expr` (= old `Expr`). Update them to work on the appropriate stage:

| Module | Input stage | Output stage |
|---|---|---|
| `apply_spine` | `LoweredExpr` (reads `.ty: typed_ir::Type`) | side effect: produces solutions |
| `cast` | `FinalizedExpr` (post-materialize) | `FinalizedExpr` (Coerce normalized) |
| `materialize` | `LoweredExpr` | `FinalizedExpr` |
| `rewrite` | `FinalizedExpr` (in place mutations after materialize) | `FinalizedExpr` |
| `role` | `FinalizedExpr` (rewrite_role_method_calls runs after materialize) | mutates in place |
| `postpass` | `FinalizedExpr` | mutates in place |

The main loop in `mod.rs::finalize_module_with_cache` consumes a `LoweredModule` and threads it through:

1. `cast_order = cast::type_cast_order(...)` — input: role_impls only, output: TypeCastOrder
2. `solve_root_graphs(&lowered_module, &cast_order)` — input: `&LoweredModule`, output: Vec<RootGraphSolution>
3. **Materialize boundary**: convert `LoweredModule` → `FinalizedModule` by materializing every Binding.body and every root_exprs entry via `materialize_expr`. This is the single "stage transition" point.
4. The rest of the loop (`canonicalize_aliases`, `append_monomorphic_bindings`, `rewrite_root_exprs`, ...) operates on `FinalizedModule`.

#### 3g. Update `cache.rs`

`FinalizeInstanceCache` stores `CachedFinalizeInstance` which currently contains `Expr` and `Type`. Both become `FinalizedExpr` and `FinalizedType`. Bump `FINALIZE_INSTANCE_CACHE_FORMAT_VERSION` since the on-disk format changes.

#### 3h. Update tests

Tests in `solver/mod.rs::mod tests` use both stages. Update them to construct `LoweredExpr` or `FinalizedExpr` explicitly. Helper builders like `Expr::typed(kind, ty)` may need duplicates: `LoweredExpr::typed(...)` and `FinalizedExpr::typed(...)`.

#### Verify

`cargo test -p yulang-runtime-finalize` must pass 70 + 1 tests.

### Step 4 — Misc cleanup

- Remove dead helpers: `restore_*` (already deleted), any helper that became unused after Core was eliminated.
- Audit `narrow_runtime_type_in_place`, `narrow_core_type_in_place`: do they still serve a purpose now that the materialization is correct from the start? If not, delete. If yes, rename for `FinalizedType`.
- Audit `merge_partial_runtime_type`, `merge_partial_core_type`: same question.
- Update `archive/notes/refactors/yulang-runtime.md` to note that monomorphize/refine/validate are now disconnected.

---

## 4. Detailed conversion algorithms

### 4.1 `materialize_finalized_type` (substitution on FinalizedType)

```rust
pub fn materialize_finalized_type(
    ty: FinalizedType,
    substitutions: &[typed_ir::TypeSubstitution],
) -> FinalizedType {
    match ty {
        FinalizedType::Unknown => FinalizedType::Unknown,
        FinalizedType::Value(t) => {
            // After substitution, t might *become* a Fun. Reroute through
            // finalized_from_typed_ir to lift it into FinalizedType::Fun.
            finalized_from_typed_ir(materialize_core_type(t, substitutions))
        }
        FinalizedType::Fun { param, ret } => FinalizedType::fun(
            materialize_finalized_type(*param, substitutions),
            materialize_finalized_type(*ret, substitutions),
        ),
        FinalizedType::Thunk { effect, value } => FinalizedType::thunk(
            materialize_core_type(effect, substitutions),
            materialize_finalized_type(*value, substitutions),
        ),
    }
}
```

### 4.2 `materialize_core_type` (unchanged)

Lives in `graph.rs`. Operates on `typed_ir::Type`. No change.

### 4.3 `finalized_from_typed_ir` (lifts Fun into Finalized form, auto-thunking)

```rust
/// Convert a typed_ir value type into its VM-shaped FinalizedType form.
/// Functions become `FinalizedType::Fun` with each side wrapped in `Thunk`
/// when its effect row is non-empty.
pub fn finalized_from_typed_ir(ty: typed_ir::Type) -> FinalizedType {
    match ty {
        typed_ir::Type::Fun { param, param_effect, ret_effect, ret } => FinalizedType::Fun {
            param: Box::new(finalized_with_effect(*param, *param_effect)),
            ret: Box::new(finalized_with_effect(*ret, *ret_effect)),
        },
        ty => FinalizedType::Value(ty),
    }
}

pub fn finalized_with_effect(value: typed_ir::Type, effect: typed_ir::Type) -> FinalizedType {
    let value = finalized_from_typed_ir(value);
    if should_thunk_effect(&effect) {
        FinalizedType::Thunk { effect, value: Box::new(value) }
    } else {
        value
    }
}
```

Replaces `runtime_type_from_core_value` and `runtime_type_from_core_value_and_effect`.

### 4.4 `finalized_to_typed_ir` (inverse)

```rust
/// Convert a FinalizedType back to its typed_ir representation.
/// Used by call-site predicates that compare against expected core types.
pub fn finalized_to_typed_ir(ty: FinalizedType) -> typed_ir::Type {
    match ty {
        FinalizedType::Unknown => typed_ir::Type::Unknown,
        FinalizedType::Value(t) => t,
        FinalizedType::Fun { param, ret } => {
            let (param_value, param_effect) = split_finalized(*param);
            let (ret_value, ret_effect) = split_finalized(*ret);
            typed_ir::Type::Fun {
                param: Box::new(param_value),
                param_effect: Box::new(param_effect),
                ret: Box::new(ret_value),
                ret_effect: Box::new(ret_effect),
            }
        }
        FinalizedType::Thunk { effect, value } => {
            // A Thunk at the top level means "this is an effected value position"
            // — but the inverse projection only encodes effect inside a Fun, so a
            // top-level Thunk loses the effect. Use split_finalized at Fun sides
            // instead.
            finalized_to_typed_ir(*value)
        }
    }
}

fn split_finalized(ty: FinalizedType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        FinalizedType::Thunk { effect, value } => (finalized_to_typed_ir(*value), effect),
        other => (finalized_to_typed_ir(other), typed_ir::Type::Never),
    }
}
```

Replaces `runtime_type_to_core`. The split helper replaces `runtime_type_to_effected_core` / `split_runtime_effected_type`.

### 4.5 Lowering (yulang-runtime/lower)

Lowering currently produces `Expr` with `ty: Type`. After refactor, it produces `LoweredExpr` (= `Expr<typed_ir::Type>`).

The change in each lowering site: where the code currently writes `Type::Core(t)`, write `t` directly. Where it currently writes `Type::Fun { .. }` or `Type::Thunk { .. }`, **it should not** — these constructions are post-finalize-only. If lowering ever produces a Fun or Thunk shape, that's a sign the lowering is doing finalize's job. Refactor that case: write the raw `typed_ir::Type::Fun { ..., param_effect, ret_effect, ... }` instead. The Thunk wrapping happens in finalize via `finalized_from_typed_ir`.

After the change, lowering's output is purely `typed_ir::Type` everywhere. Simpler.

---

## 5. Known gotchas

### 5.1 Serde with generics

`#[derive(Serialize, Deserialize)]` on `Expr<T>` requires `T: Serialize` (and `for<'de> T: Deserialize<'de>` for Deserialize). Both `typed_ir::Type` and `FinalizedType` derive these — should just work. If you hit `#[serde(bound = "...")]` issues, add explicit bounds.

### 5.2 Non-recursive Clone

The existing `Clone for Expr` uses an explicit frame stack to avoid stack overflow on deep Apply spines (see the existing `clone_expr_without_apply_spine_recursion` test in `runtime-ir/src/lib.rs`). Carry this pattern forward when generic-izing. The frame enum's fields hold `&'a T` for type slots (param ty, etc.). The corresponding `clone_type_without_fun_spine_recursion` test should be ported to `FinalizedType`.

### 5.3 `HashMap<Path, FinalizedType>` etc.

`FinalizedType: Hash + Eq` is derivable (all variants' fields support Hash+Eq when `typed_ir::Type` does, which it does). Just verify the derive works.

### 5.4 The `path_from_name` / `unit_type` helpers stay in `solver/mod.rs::postpass`

They don't depend on the type parameter; nothing changes there.

### 5.5 `ApplyEvidence` etc. are `typed_ir::` items

`typed_ir::ApplyEvidence` is referenced inside `ExprKind::Apply`. Since it's a `typed_ir` item with `typed_ir::Type` slots, it's unaffected by the `T` parameter. (Apply evidence carries infer-form type info either way — it's not stage-dependent.)

### 5.6 `JoinEvidence` stays scalar `typed_ir::Type`

Same reason. The `result: typed_ir::Type` field is infer-form even post-finalize because Match/If join results are stored as typed_ir types in the IR.

If post-finalize wants `result: FinalizedType` instead, that's a separate change and not part of this refactor. For now, JoinEvidence is stage-agnostic.

### 5.7 Recursive Box<Type<T>> in `FinalizedType`

`FinalizedType::Fun` and `Thunk` hold `Box<FinalizedType>`. This is fine — Rust handles recursive enum types as long as there's a Box indirection.

### 5.8 Don't accidentally re-introduce Core via `Value(typed_ir::Type::Fun { .. })`

The constructor `FinalizedType::value(ty)` has a `debug_assert!` to catch this. The conversion function `finalized_from_typed_ir` always lifts Fun out. As long as construction goes through these helpers, the invariant holds.

If any code path needs to construct `FinalizedType::Value` from a value that *might* be a Fun, it should go through `finalized_from_typed_ir` instead. Replace direct `FinalizedType::Value(t)` constructions with `finalized_from_typed_ir(t)` if `t`'s shape is uncertain.

### 5.9 The CLI driver's `runtime_finalize_ir` print path

`crates/yulang/src/main.rs` has a `--runtime-finalize-ir` flag that prints the lowered (pre-finalize) IR. After refactor, this prints `LoweredModule`. The display impl needs to handle `Module<typed_ir::Type>` — likely just `Debug` is fine.

The `--runtime-ir` flag prints the finalized form (`FinalizedModule`). Similar adjustment.

---

## 6. Verification criteria

The refactor is complete when **all** of the following hold:

1. `cargo build --workspace` succeeds (modulo `unimplemented!()` panics in disconnected `yulang-runtime` modules).
2. `cargo test -p yulang-runtime-finalize` passes with **70 passed; 0 failed; 1 ignored**. (Baseline before refactor; should match exactly.)
3. `cargo test -p yulang-runtime-ir` passes its one existing test (`clones_deep_runtime_adapter_spine_without_recursing`, ported to `FinalizedType`).
4. `grep -rn 'restore_runtime_effect_boundaries\|restore_apply_spine_arg_effects\|restore_apply_arg_effect' crates/` returns no matches (functions deleted).
5. `grep -rn 'Type::Core\|RuntimeType::Core' crates/yulang-runtime-finalize/src/` returns no matches (Core variant eliminated).
6. The `solved_callee_finalized_type` (renamed from `solved_callee_runtime_type`) no longer needs a restore-style postcondition; the principal-derived form is correct as-is.

Optional polish (not blockers):

- `apply_spine.rs` and `postpass.rs` further sub-split (see `notes/todo.md`).
- `materialize_runtime_type` in `graph.rs` (now `materialize_finalized_type`) — verify it really preserves Fun/Thunk structure under substitution without losing effect info. Add a unit test.

---

## 7. Out of scope (future work)

- Re-enabling `yulang-runtime::monomorphize/refine/validate`: the user has indicated this crate will be rewritten or replaced. This refactor leaves those modules stubbed with `unimplemented!()` for now.
- Updating `yulang-vm`, `yulang-compile`: these crates don't directly import `runtime_ir::Type`, but if they grow to consume the finalized IR, they'll need the new aliases.
- Bridging `FinalizedType` to a future `vm_ir` shape: out of scope. The VM rewrite will define its own shape.

---

## 8. Glossary

- **Lowered (form)**: post-lowering / pre-finalize. `Expr<typed_ir::Type>`. Effects are explicit in `typed_ir::Type::Fun.param_effect/ret_effect`. No Thunk wrappers in `.ty`.
- **Finalized (form)**: post-finalize / VM-ready. `Expr<FinalizedType>`. Effects encoded by `FinalizedType::Thunk` wrappers at Fun param/ret positions.
- **Restore**: the historical post-pass that re-injected Thunks lost during materialization. **Will not exist after this refactor.**
- **Stage transition point**: the single function call inside `finalize_module_with_cache` that materializes a `LoweredModule` → `FinalizedModule`. After this point, only finalized form is used.

---

## 9. Suggested commit structure

Single commit acceptable, but if the diff is too large, split:

1. `runtime-ir: add FinalizedType and parameterize Expr/Module over T`
2. `runtime: stub monomorphize/refine/validate; update lower to produce LoweredModule`
3. `runtime-finalize: switch to LoweredExpr/FinalizedExpr; delete restore_*`
4. `notes: mark monomorphize/refine/validate as disconnected`

Each commit should compile (Step 1 standalone, Steps 2 and 3 might need to be one commit if interdependent).

Co-Author tag if applicable.
