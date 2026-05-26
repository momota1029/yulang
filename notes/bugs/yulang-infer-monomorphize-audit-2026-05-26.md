# yulang-infer / yulang-monomorphize audit notes

Date: 2026-05-26

Scope:

- `crates/yulang-infer`
- `crates/yulang-monomorphize`

This is a read-only audit note. No behavior was changed while writing it.

## High-confidence issues

### 1. `Any` is treated as both top and bottom in monomorphize subtyping

Location:

- `crates/yulang-monomorphize/src/graph.rs:302`
- `crates/yulang-monomorphize/src/graph.rs:303`
- `crates/yulang-monomorphize/src/graph.rs:304`

Problem:

`apply_subtype_constraint_inner` returns success when either `upper` or `lower` is `Any`.
`upper == Any` is valid because `Any` is Top. `lower == Any` is not generally valid:
`Any <: T` should only hold when `T` is also Top or an equivalent top-like type.

This makes `Any` behave like an "unknown / flexible" type, which violates the Yulang
type meaning rules.

Fix direction:

Keep `(_, Any)` as vacuous upper-bound success, but do not treat `(Any, _)` as success.
For `Any <: concrete`, record a conflict or keep it as a real upper/lower constraint that
must fail unless the target is also Top.

### 2. Runtime-bound collection ignores variance inside function types

Location:

- `crates/yulang-monomorphize/src/graph.rs:193`
- `crates/yulang-monomorphize/src/graph.rs:208`
- `crates/yulang-monomorphize/src/graph.rs:209`
- `crates/yulang-monomorphize/src/graph.rs:210`
- `crates/yulang-monomorphize/src/graph.rs:211`

Problem:

`collect_core(template, actual, side)` descends through a function type using the same
`side` for parameter, parameter effect, return effect, and return value.

But function parameter positions are contravariant. A lower/upper observation for the
whole function cannot be pushed into `param` with the same polarity. The subtype path
does handle parameter reversal later (`graph.rs:354`), but `collect_runtime_bounds`
bypasses that by recording bounds directly.

Likely symptom:

Type parameters that occur only or mainly in function parameter positions can be solved
from the wrong side, producing aliases that are too specific or have backwards cast/coerce
behavior.

Fix direction:

Replace `collect_core` with a polarity-aware traversal, or express runtime observations as
subtype constraints and let the subtype decomposer handle variance. Function `param`
must flip polarity. Effect positions need the same explicit variance decision as the core
type theory.

### 3. Shape mismatches are silently ignored in `TypeGraph`

Location:

- `crates/yulang-monomorphize/src/graph.rs:141`
- `crates/yulang-monomorphize/src/graph.rs:148`
- `crates/yulang-monomorphize/src/graph.rs:182`
- `crates/yulang-monomorphize/src/graph.rs:185`
- `crates/yulang-monomorphize/src/graph.rs:199`
- `crates/yulang-monomorphize/src/graph.rs:205`
- `crates/yulang-monomorphize/src/graph.rs:214`
- `crates/yulang-monomorphize/src/graph.rs:217`
- `crates/yulang-monomorphize/src/graph.rs:423`

Problem:

Several branches return `Ok(())` or `Ok(false)` when the template and actual shapes do
not match. This loses evidence instead of producing a conflict or preserving a constraint.

Examples:

- runtime `Fun` observed against a non-function template returns `Ok(())`
- named constructors with different paths or arg counts return `Ok(())`
- tuple arity mismatch returns `Ok(())`
- final subtype shape mismatch falls into `_ => Ok(false)`

Fix direction:

Mismatched closed shapes should become `ConflictingBounds` or a dedicated graph diagnostic.
Open shapes can wait only when the mismatch is actually caused by `Unknown` or an unsolved
type variable.

### 4. `Union` / `Intersection` subtyping is only half implemented

Location:

- `crates/yulang-monomorphize/src/graph.rs:393`
- `crates/yulang-monomorphize/src/graph.rs:400`

Problem:

The solver handles:

- `Union(items) <: upper` by requiring every item to be below `upper`
- `lower <: Inter(items)` by requiring `lower` below every item

It does not handle the dual elimination/introduction cases:

- `Inter(items) <: upper`
- `lower <: Union(items)`

Those are needed for normal lattice behavior. Some helper scoring code handles upper
unions, so the implementation is internally inconsistent.

Fix direction:

Add principled rules for both directions, or normalize away union/intersection before
runtime-finalize if they are not meant to reach this layer.

### 5. `Any` is explicitly rewritten to `Unknown` in apply-spine solving

Location:

- `crates/yulang-monomorphize/src/solver/apply_spine.rs:1048`
- `crates/yulang-monomorphize/src/solver/apply_spine.rs:1051`
- `crates/yulang-monomorphize/src/solver/apply_spine.rs:1096`
- `crates/yulang-monomorphize/src/solver/apply_spine.rs:1097`
- `crates/yulang-monomorphize/src/solver/apply_spine.rs:1098`

Problem:

`apply_callee_lower_bound` / `unconstrain_top_param_core_bound` turn `Any` in parameter
slots into `Unknown`.

The comment says the `Any` is "not an instantiation lower bound", but changing Top into a
hole is the wrong layer boundary. It hides the actual issue: the callee occurrence is
being used as a lower-bound source without respecting function parameter polarity.

Fix direction:

Remove this conversion after fixing polarity-aware bound collection. If a parameter slot
is Top due to contravariance, the graph should avoid recording it as a lower value bound
instead of mutating the type meaning.

### 6. Defaulting unresolved graph variables to `Unknown` is ineffective and conceptually wrong

Location:

- `crates/yulang-monomorphize/src/solver/apply_spine.rs:615`
- `crates/yulang-monomorphize/src/solver/apply_spine.rs:624`
- `crates/yulang-monomorphize/src/graph.rs:686`

Problem:

`default_unbound_lower(..., Type::Unknown)` appears to default unbound slots, but `record`
immediately ignores `Unknown` bounds. So the call does not actually make the graph
complete.

Even if it did, `Unknown` should mean "still unresolved", not a monomorphic solution.

Fix direction:

Delete the fake defaulting. If a variable cannot be solved, keep `IncompleteGraph` and
fix the missing evidence path. Only default effect-only variables to `Never` when that is
the actual pure-effect bottom rule.

### 7. Variant and record constraints drop missing cases/fields

Location:

- `crates/yulang-monomorphize/src/graph.rs:565`
- `crates/yulang-monomorphize/src/graph.rs:571`
- `crates/yulang-monomorphize/src/graph.rs:572`
- `crates/yulang-monomorphize/src/graph.rs:581`
- `crates/yulang-monomorphize/src/graph.rs:591`
- `crates/yulang-monomorphize/src/graph.rs:597`
- `crates/yulang-monomorphize/src/graph.rs:602`
- `crates/yulang-monomorphize/src/graph.rs:610`
- `crates/yulang-monomorphize/src/graph.rs:617`
- `crates/yulang-monomorphize/src/graph.rs:618`
- `crates/yulang-monomorphize/src/graph.rs:621`
- `crates/yulang-monomorphize/src/graph.rs:651`
- `crates/yulang-monomorphize/src/graph.rs:658`
- `crates/yulang-monomorphize/src/graph.rs:663`

Problem:

`collect_variant`, `collect_record`, `constrain_variant`, and `constrain_record` mostly
process matching names and skip missing names or payload-count mismatches.

This is only sound if an explicit open tail/spread proves that the missing part may exist.
The code often ignores the tail/spread distinction and never reports conflicts for closed
missing cases/fields.

Fix direction:

Make record/variant constraints tail-aware:

- closed lower variant must not contain a case that the upper closed variant lacks
- closed record lower must satisfy required upper fields
- payload length mismatch should be a conflict
- open tails/spreads should receive residual constraints instead of silent `continue`

### 8. Infer row subtraction constrains the tail with already-matched negative items

Location:

- `crates/yulang-infer/src/solve/constrain/rows.rs:17`
- `crates/yulang-infer/src/solve/constrain/rows.rs:21`
- `crates/yulang-infer/src/solve/constrain/rows.rs:27`
- `crates/yulang-infer/src/solve/constrain/rows.rs:29`
- `crates/yulang-infer/src/solve/constrain/rows.rs:64`
- `crates/yulang-infer/src/solve/constrain/rows.rs:65`

Problem:

The row solver cancels matched positive/negative items into `neg_unmatched`, but when it
constrains `pos_tail`, it uses `original_neg_items` instead of `neg_unmatched`.

That means a row item already provided by the concrete positive prefix is required again
from the tail.

Fix direction:

Use `neg_unmatched` when building the negative residual row for `pos_tail`. Keep
`original_neg_items` only if there is a separate invariant that requires the tail to
re-prove the entire upper row, which would be unusual for row subtraction.

### 9. Constructor arity mismatch is ignored in infer

Location:

- `crates/yulang-infer/src/solve/constrain/shape.rs:126`
- `crates/yulang-infer/src/solve/constrain/shape.rs:128`
- `crates/yulang-infer/src/solve/constrain/shape.rs:131`

Problem:

When `Pos::Con` and `Neg::Con` have the same path, the solver zips args and never checks
that `p_args.len() == n_args.len()`.

A malformed or partially lowered constructor type can therefore satisfy a different arity
without a diagnostic.

Fix direction:

Check arity before variance propagation and report a constructor/type-arg arity mismatch.

### 10. PolyVariant subtype checks ignore missing tags and payload mismatches

Location:

- `crates/yulang-infer/src/solve/constrain/shape.rs:97`
- `crates/yulang-infer/src/solve/constrain/shape.rs:98`
- `crates/yulang-infer/src/solve/constrain/shape.rs:99`
- `crates/yulang-infer/src/solve/constrain/shape.rs:102`

Problem:

For `Pos::PolyVariant <: Neg::PolyVariant`, the solver iterates positive tags and only
constrains matching negative tags. Missing tags and payload-count mismatches are ignored.

That makes a value with tag `A` compatible with a consumer that only accepts tag `B`.

Fix direction:

If `Neg::PolyVariant` is closed, every positive tag must exist in the negative variant
with the same payload arity. If variants are meant to be open, the IR needs an explicit
tail like runtime `typed_ir::VariantType` has.

### 11. Constraints involving `Forall` are dropped

Location:

- `crates/yulang-infer/src/solve/constrain.rs:163`
- `crates/yulang-infer/src/solve/constrain/frozen.rs:59`

Problem:

`Pos::Forall` or `Neg::Forall` in a constraint causes the solver to do nothing.

If `Forall` can reach the constraint engine, this is unsound: a polymorphic producer or
consumer must be instantiated, skolemized, packed/unpacked, or rejected. No-op means
constraints disappear.

Fix direction:

Define the exact phase where `Forall` is eliminated. If it is legal in constraints, add
explicit rules. If it is illegal, report an internal diagnostic/assertion instead of
silently accepting it.

### 12. Substitution under `Forall` does not respect binders

Location:

- `crates/yulang-infer/src/scheme/view.rs:37`
- `crates/yulang-infer/src/scheme/view.rs:139`
- `crates/yulang-infer/src/scheme/instantiate.rs:197`
- `crates/yulang-infer/src/scheme/instantiate.rs:286`
- `crates/yulang-infer/src/scheme/instantiate.rs:352`
- `crates/yulang-infer/src/scheme/instantiate.rs:446`
- `crates/yulang-infer/src/scheme/freeze.rs:535`
- `crates/yulang-infer/src/scheme/freeze.rs:642`

Problem:

Several substitution/clone paths recurse into `Forall` bodies with the same substitution.
Some also substitute the bound variable list itself.

For a binding construct, substitutions must not rewrite variables bound by that construct
inside the body unless the binder is deliberately alpha-renamed first. Current code risks
capturing or rewriting locally quantified variables.

Fix direction:

When entering `Forall(vars, body)`, remove `vars` from the active substitution. If the
destination context can collide, alpha-rename the quantified variables and then substitute
the body with the extended rename.

### 13. Extrusion ignores variables inside effect atoms and `Forall`

Location:

- `crates/yulang-infer/src/solve/constrain/extrude.rs:23`
- `crates/yulang-infer/src/solve/constrain/extrude.rs:81`
- `crates/yulang-infer/src/solve/constrain/extrude.rs:127`
- `crates/yulang-infer/src/solve/constrain/extrude.rs:198`

Problem:

`max_level_pos` / `max_level_neg` treat `Atom(_)` as level `0`, even though
`EffectAtom.args` contains type variables. `lower_levels_pos` / `lower_levels_neg` also
do nothing for `Atom(_)`. They also skip `Forall(..)` entirely when lowering levels, even
though `max_level_*` descends into `Forall` bodies.

This can leave higher-level variables inside effect atoms or quantified bodies after
extrusion.

Fix direction:

Traverse `EffectAtom.args` in max/lower level passes. For `Forall`, either do not count
the body in `max_level_*`, or lower/freshen body variables in a binder-aware way.

### 14. Role method candidate matching treats unsolved vars as matching everything

Location:

- `crates/yulang-monomorphize/src/solver/role.rs:936`
- `crates/yulang-monomorphize/src/solver/role.rs:943`
- `crates/yulang-monomorphize/src/solver/role.rs:945`

Problem:

`core_subtype_match_score` gives `Some(2)` whenever either side is `Type::Var(_)`.
This is used for role method dispatch scoring. An unsolved variable therefore makes a
candidate look applicable instead of forcing the solver to wait for more evidence.

Fix direction:

Do not accept unresolved vars as positive dispatch evidence. Treat them as "not ready"
unless the variable belongs to the candidate template and is being solved by an explicit
unifier.

### 15. Local type repair uses a flat path scope and loses shadowed bindings

Location:

- `crates/yulang-monomorphize/src/solver/postpass.rs:452`
- `crates/yulang-monomorphize/src/solver/postpass.rs:458`
- `crates/yulang-monomorphize/src/solver/postpass.rs:562`
- `crates/yulang-monomorphize/src/solver/postpass.rs:568`
- `crates/yulang-monomorphize/src/solver/postpass.rs:581`
- `crates/yulang-monomorphize/src/solver/postpass.rs:621`
- `crates/yulang-monomorphize/src/solver/postpass.rs:628`
- `crates/yulang-monomorphize/src/solver/postpass.rs:631`

Problem:

`fill_local_var_types` says a flat name-to-type scope is safe because hygiene prevents
shadowing collisions, but block `let` pattern bindings are inserted without saving the
previous binding for the same path. At block exit, the path is removed, so an outer binding
with the same one-segment name is lost.

Lambda parameters handle save/restore, but block/match/handle pattern bindings do not.

Fix direction:

Use a scoped stack or save/restore entries for all pattern-introduced locals, not only
lambda params. Better yet, key locals by a lowering-time local identifier instead of
`Path::from_name`.

### 16. Materialization uses `Unknown` as a shape wildcard for coercion/thunk adaptation

Location:

- `crates/yulang-monomorphize/src/solver/materialize.rs:1086`
- `crates/yulang-monomorphize/src/solver/materialize.rs:1096`
- `crates/yulang-monomorphize/src/solver/materialize.rs:1114`
- `crates/yulang-monomorphize/src/solver/materialize.rs:1154`
- `crates/yulang-monomorphize/src/solver/materialize.rs:1156`
- `crates/yulang-monomorphize/src/solver/materialize.rs:1157`

Problem:

`materialized_core_shapes_match` returns true if either side is `Unknown` or a type var.
That predicate gates thunk wrapping, thunk forcing, and value coercion.

This can adapt an expression across an unresolved type hole, which may hide the missing
constraint and produce a runtime-shaped expression that looks valid but was not proven.

Fix direction:

Only use shape matching for closed concrete shapes. If a side is `Unknown`, skip adaptation
and keep the graph incomplete earlier, or require explicit evidence that the adaptation is
legal.

### 17. Debug invariant validation is effectively non-failing

Location:

- `crates/yulang-monomorphize/src/solver/mod.rs:90`
- `crates/yulang-monomorphize/src/solver/mod.rs:91`
- `crates/yulang-monomorphize/src/solver/mod.rs:95`
- `crates/yulang-monomorphize/src/solver/mod.rs:118`

Problem:

`monomorphize_module_with_report` discards the result of `validate_monomorphized_output`.
The validator only runs when `YULANG_FINALIZE_DEBUG_INVARIANTS` is set, and even then it
prints to stderr instead of returning an error.

This makes invariant checks unable to protect tests or callers.

Fix direction:

Make invariant validation return `MonomorphizeDiagnostic` values and propagate them in
debug/test modes. If it is intentionally advisory, rename it so it is not mistaken for a
real validator.

## Medium-confidence issues / follow-up targets

### 18. `collect_type_arg` and `constrain_type_arg` do not use declared variance

Location:

- `crates/yulang-monomorphize/src/graph.rs:427`
- `crates/yulang-monomorphize/src/graph.rs:473`

Problem:

Type arguments are traversed structurally, but this graph has no constructor variance
table like `yulang-infer::Infer::variances`. If runtime-finalize can see generic
constructors with non-invariant parameters, type-arg solving can be wrong.

Fix direction:

Carry constructor variance into monomorphize/finalize, or require the typed IR to
pre-normalize generic arguments into explicit bounds that no longer need constructor
variance.

### 19. Bound conflict handling ignores many var-containing conflicts

Location:

- `crates/yulang-monomorphize/src/graph.rs:1369`
- `crates/yulang-monomorphize/src/graph.rs:1375`
- `crates/yulang-monomorphize/src/graph.rs:1378`
- `crates/yulang-monomorphize/src/graph.rs:1382`

Problem:

`push_bound` ignores conflicting bounds when both are vars, when the new bound is a var
and previous is concrete, or when either bound contains a var.

This avoids cycles, but it also drops constraints that should remain in the graph. The
later `IncompleteGraph` only sees missing solutions, not the reason the constraint was
discarded.

Fix direction:

Represent pending var-containing bounds explicitly instead of dropping them. Cycle
avoidance should be in graph traversal, not by erasing constraints.

### 20. Export paths erase open variables to `Unknown`

Location:

- `crates/yulang-infer/src/export/type_props.rs:314`
- `crates/yulang-infer/src/export/type_props.rs:327`
- `crates/yulang-infer/src/export/type_props.rs:330`
- `crates/yulang-infer/src/export/type_props.rs:333`
- `crates/yulang-infer/src/export/type_props.rs:336`
- `crates/yulang-infer/src/export/types.rs:583`
- `crates/yulang-infer/src/export/types.rs:587`
- `crates/yulang-infer/src/export/types.rs:590`
- `crates/yulang-infer/src/export/types.rs:594`

Problem:

Several export helpers collapse unresolved/open variables into `Type::Unknown`. This may
be acceptable at a display or diagnostic boundary, but it is risky if the exported typed
IR is later used as semantic input for runtime lowering or monomorphize.

Fix direction:

Audit each caller and split the APIs:

- display/diagnostic projection may erase to `Unknown`
- semantic export should preserve variables or produce an explicit "not closed" result

## Suggested order of repair

1. Fix monomorphize `Any`/`Unknown` handling and remove `Any -> Unknown` conversion.
2. Replace `TypeGraph::collect_core` with a polarity-aware constraint traversal.
3. Make row/record/variant residual handling explicit in both infer and monomorphize.
4. Stop dropping `Forall` constraints; define the legal elimination point.
5. Replace flat local-name repair scopes with scoped local IDs or save/restore stacks.
6. Turn invariant validation into real test-visible errors.

## Tests to add when fixing

- `Any <: int` must fail or stay unsolved; `int <: Any` must succeed.
- A polymorphic function whose type parameter appears only in a function parameter should
  not be solved from the wrong polarity.
- Row with a matched effect item and open tail should not require the matched item twice.
- Closed variant `#A` should not satisfy closed variant `#B`.
- Same constructor path with mismatched type-arg arity should report an error.
- Nested `Forall` substitution should not rewrite bound variables.
- Shadowed block locals should keep the outer local type after the block exits.

---

## Progress log — follow-up session 2026-05-26 (post-audit)

Working tree state at the time of this log: 34 files modified (Codex's in-progress
fixes from the original audit run, unstashed). Note: do NOT assume the diff is
clean; the changes below describe what is already in the working tree.

### Items already addressed by Codex in the working tree (verified)

- **Issue #1 (`Any` treated as both top and bottom)**: the early-exit short-circuit
  `matches!(lower, typed_ir::Type::Any)` previously added by commit `f5b428d`
  (a symptomatic workaround) has been removed from
  `crates/yulang-monomorphize/src/graph.rs` (line 310 area). In its place,
  `reject_invalid_top_bottom_bounds` produces a real `ConflictingBounds`
  diagnostic when `Any <: V` collides with a concrete upper bound.
  Regression test added: `any_lower_bound_conflicts_with_concrete_upper_bound`.
- **Issue #2 (variance ignored in `collect_core` / `collect_runtime`)**: a new
  `BoundSide::flip()` is threaded through both collectors so parameter positions
  flip polarity. A `runtime_value_is_top` guard avoids recording `Any` as a
  lower bound after the flip. Regression tests added:
  `function_runtime_lower_bound_flips_parameter_polarity` and
  `function_runtime_lower_bound_does_not_turn_top_parameter_into_solution`.
- **Issue #4 (Union/Inter half implementation)**: `normalize_bound_form_inner`
  is now tail-aware for `Row` / `Union` / `Inter`, flattening nested unions
  and intersections into the outer normal form.
- **Issue #5 (apply-spine rewrites `Any → Unknown`)**: superseded by #1 + #2;
  the explicit `Any → Unknown` conversion paths in `apply_spine.rs` are no
  longer needed once polarity is correct, and several were removed.
- **Issue #8 (row subtraction uses original instead of unmatched)**: fixed in
  `crates/yulang-infer/src/solve/constrain/rows.rs` (now constrains pos_tail
  with `neg_unmatched`).

### Latent cache-invalidation hazard (independent of the audit items)

Commit `d9ba7e9` changed primitive scheme bodies (`list.rs` / `scalar.rs`) to
emit `Type::Never` instead of `Type::Any` in `param_effect` / `ret_effect`
slots. The change is Rust-side only, but the persistent test cache at
`target/yulang/test-cache/std-runtime-ir/` is keyed by source hash and
`artifact_format_version` (currently `17`), neither of which budged. Older
cached artifacts still served `std::list::index_raw` with `param_effect: Any`,
which the new monomorphize correctly rejected via `ConflictingBounds`
(prior workaround had silently dropped these `Any` lowers).

Reproduce: with a pre-d9ba7e9 cache directory present, run
`cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples`
→ panics with `ConflictingBounds { var: apply_effect#2, previous: Any, next:
Row { items: [std::var::ref_update] } }`. Wiping `target/yulang/test-cache/`
makes it pass. Recommended fix: bump `artifact_format_version`, or fold a
build-time hash of primitive scheme tables into the cache key, whenever
Rust-side schemes change in a way that affects the emitted typed IR. Without
this, every developer who runs into similar regressions has to remember the
incantation `rm -rf target/yulang/test-cache`.

### Unresolved: monomorphize `materialize.rs` thunk-adaptation regression

**Symptom**: with a clean cache and the current working tree, the test
`solver::tests::cached_std_finalize_runs_playground_core_examples` fails on
case `undet once range`:

```
expected = ["just 3"]
actual   = ["<request std::undet::undet::branch>"]
```

I.e. `branch()` inside `each 1..` is not caught by the `.once` handler — it
escapes all the way to the program root unhandled.

**Minimal repro** (place in `/tmp/undet_once.yu`):

```yulang
use std::undet::*
{
    my a = each 1..
    guard: a == 3
    a
}.once
```

```sh
rm -rf target/yulang/test-cache
cargo run -q -p yulang -- run --print-roots --no-cache /tmp/undet_once.yu
# expected: [0] just 3
# actual:   [0] request std::undet::undet::branch () blocked=None
```

**What I traced** (using throwaway eprintln in `vm/control.rs`):

1. `finalized IR dump` shows `once::mono1.body =
   Lambda(x) { LocalPushId { Thunk { Block { let loop = Lambda(x → Lambda(queue → catch x: …)); loop x [] } } } }`
   — i.e. the `catch` arms `branch / reject / value` are present in the IR.
2. At runtime, `eval_handle` fires exactly once with arms `[sub::return, value]`
   (the `sub::sub` handler inside `each`'s body). The `once` `catch` arms
   `[branch, reject, value]` are never installed: `eval_handle` is never
   called with them.
3. `eval_var` shows only `once::mono1` and `each::mono0` are entered. The
   nested `loop` binding from `once`'s `with:` block is never applied.
4. From the apply trace, the body inside `Thunk` (ExprId 306 in my run) does
   not execute `loop x []`; it goes straight to calling `each` and then
   threading the result through primitives.

**Why this points at `materialize.rs`**: stash-pop comparison confirms
HEAD passes the same source. Reverting only
`crates/yulang-monomorphize/src/solver/materialize.rs` to HEAD (keeping every
other working-tree change) makes both `undet once range` and the original
Any-conflict regressions pass. The culprit is the working tree's new
`materialize_thunk_to_value_or_coerce` + `materialized_core_shapes_match`
machinery, introduced to address audit item #16.

**The catch — can't just revert materialize.rs**: doing so makes
`std_no_cache_finalize_runs_reported_graph_unification_regressions` fail on
case `list index raw preserves callback function element` with
`IncompleteGraph { binding: std::list::index_raw }`. Codex's other
working-tree changes (most likely `apply_spine.rs`, `+265 lines`) rely on the
new materialize machinery to forcibly bridge Thunk ↔ value at the right
boundary. Partial in-place edits in `materialize.rs` alone could not
simultaneously satisfy both regressions:

| materialize.rs state                                | undet | Any conflict | list index raw |
| --------------------------------------------------- | ----- | ------------ | -------------- |
| HEAD                                                | ok    | n/a          | ok             |
| Codex working tree (current)                        | fail  | ok           | ok             |
| ガード残し + `BindHere` force 削除                  | ok    | ok           | fail           |
| ガードなし + `BindHere` force なし                  | ok    | ok           | fail           |
| ガードなし + `BindHere` force あり (中間試行)       | fail  | —            | —              |

So the `materialize_thunk_to_value_or_coerce` `BindHere` path is necessary
for `list index raw` and yet over-eager for the `once` thunk argument. The
discriminator the current code uses (`materialized_core_shapes_match`) is
too coarse: it returns `true` whenever either side is `Unknown` or `Var(_)`,
which is exactly the shape an `[_] _` thunk argument shows up with.

### Recommended next moves for the follow-up Codex session

1. **Narrow the `materialize_thunk_to_value_or_coerce` force trigger**. Today
   it BindHere-forces any `Thunk[E, V]` expression as long as `V` and the
   call-site `expected` match shape-wise. That includes the case where the
   caller is itself an `[_] _` parameter — the very case that breaks `once`.
   A safer rule: only insert `BindHere` when the call-site `expected` is a
   value type that is *not* itself a thunk slot of an `[_] _` parameter,
   and when the source `Thunk` was synthesized as an adapter (not a
   user-written thunk that needs to remain suspended for handler scope).
2. **Carry an explicit "force allowed" hint into `materialize_apply_arg`**
   rather than deriving it from runtime shapes alone. Apply-spine knows
   whether the parameter slot is a propagating `[_] _` or a concrete force
   target; pass that bit through instead of re-inferring it inside
   `materialize.rs`.
3. After fixing, rerun the three pivot tests:
   - `cargo test -p yulang-monomorphize --lib cached_std_finalize_runs_playground_core_examples`
   - `cargo test -p yulang-monomorphize --lib cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples`
   - `cargo test -p yulang-monomorphize --lib std_no_cache_finalize_runs_reported_graph_unification_regressions`
   then the whole `cargo test -p yulang-monomorphize --lib -- --test-threads=1`
   (the suite needs serial execution because the std artifact cache is shared
   under a global mutex).

### Useful instrumentation hooks left in graph.rs

Codex's working tree already includes a `YULANG_TRACE_ANY_BOUNDS=1`
environment-variable trace in `crates/yulang-monomorphize/src/graph.rs`
`record()` that prints a backtrace whenever an `Any` is about to be recorded
as a lower bound. Keep this around while debugging — it was decisive for
locating the cache-invalidation issue.

For the materialize regression, the most informative ad-hoc traces were:
- `eval_var` in `vm/control.rs` — see which bindings are entered
- `apply` in `vm/control.rs` — see which `ControlClosure.body` ExprId is
  invoked and whether `param_forces_thunk_arg` matches expectation
- `eval_handle` and `handle_request` in `vm/control.rs` — see which handler
  frames are installed and which requests propagate past them

These were all in/out scratch eprintlns; not committed.
