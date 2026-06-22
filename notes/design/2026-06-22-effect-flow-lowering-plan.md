# Effect Flow Lowering Plan

This note plans the lowering-side fix for the gap between the directed stack
weight proof and the current Rust implementation.

The short version:

- Do not remove `push(Empty)` markers. They are principal information.
- Do not reintroduce `pop(n) -> pop(1)` clamps.
- Do not broaden var-var replay to weight-insensitive `(lower, upper)` no-op.
- Remove administrative effect join variables from the replay graph by lowering
  expression effects through an explicit flow/fan-out layer.

## Problem Statement

The proof in
`research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`
proves termination for a row-only fact machine after effect sequences are
lowered to a fan-out/provenance normal form.

The current Rust lowering often materializes sequencing as a fresh `TypeVar`:

```text
part_1.effect <: join
part_2.effect <: join
...
join <: consumer
```

That join is administrative: it represents sequencing, block/catch result
collection, or a defined-lambda body proxy. It is not intended to be a semantic
row variable in the inferred scheme. However, it currently enters
`ConstraintMachine` as an ordinary variable, so replay can see cycles that do
not exist in the proof's fan-out graph.

The failure mode is:

```text
call_effect
  -- push_u(Empty) -->
application result join
  -- zero administrative aliases -->
defined lambda body/output proxy
  -- pop_u -->
call_effect
```

Exact replay then generates a pop-only alias family with growing counters. The
current `(lower, upper, pop-id-list, right-weight)` replay key cuts this after
the fact, but the root mismatch is lowering/provenance, not stack algebra.

## What We Already Ruled Out

- Removing the unannotated local callee call-result `push(Empty)` is wrong.
  It loses the required `#4[Empty]` marker in
  `std_ref_update_method_body_lowers` and leaks `ref_update` into the callback
  effect.
- Weight-insensitive replay no-op by `(lower, upper)` is too broad.
  It also loses that marker.
- `pop(n) -> pop(1)` clamp is not a semantic rule and must stay removed.

These are regression facts, not just design preferences.

## Target Invariant

Only semantic effect rows may become solver `TypeVar`s.

Administrative effect flow must remain outside `ConstraintMachine` until it is
directly connected to a semantic consumer.

More concretely:

- A variable that can appear in a principal scheme remains a `TypeVar`.
- A handler residual tail remains a `TypeVar`.
- A function return effect slot remains a `TypeVar`.
- A block/application/catch/defined-skeleton sequencing port should be an
  `EffectFlowId`, not a solver `TypeVar`, unless it is explicitly materialized
  at a semantic boundary.
- Filling a flow hole fans out existing producers to existing consumers; it does
  not create a replay-visible alias node.

## Core Representation

Introduce a lowering-only effect flow table owned by `ExprLowerer`.

Draft shape:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct EffectFlowId(u32);

pub(super) enum EffectFlow {
    Empty,
    Var(TypeVar),
    Pos(PosId),
    Seq(SmallVec<[EffectFlowId; 4]>),
    Hole(EffectFlowHole),
}

pub(super) struct EffectFlowHole {
    producers: Vec<EffectProducer>,
    consumers: Vec<EffectConsumer>,
}

pub(super) struct EffectProducer {
    pos: PosId,
    origin: EffectOrigin,
}

pub(super) struct EffectConsumer {
    neg: NegId,
    origin: EffectOrigin,
}
```

The exact Rust API may differ, but the contract should not:

```text
add_producer(hole, p):
  for c in hole.consumers:
    emit p <: c
  store p

add_consumer(hole, c):
  for p in hole.producers:
    emit p <: c
  store c
```

This is the concrete implementation of the proof-level fan-out quotient:

```text
x_i --b_i--> join --c_k--> y_k
```

is emitted as:

```text
x_i --b_i ; c_k--> y_k
```

with no solver node for `join`.

## Computation Migration

Current:

```rust
pub struct Computation {
    pub expr: ExprId,
    pub value: TypeVar,
    pub effect: TypeVar,
    pub effect_view: Option<EffectViewId>,
    pub evaluation: Evaluation,
}
```

Planned transitional shape:

```rust
pub struct Computation {
    pub expr: ExprId,
    pub value: TypeVar,
    pub effect: TypeVar,        // temporary materialized compatibility slot
    pub effect_flow: EffectFlowId,
    pub effect_view: Option<EffectViewId>,
    pub evaluation: Evaluation,
}
```

During migration, direct `.effect` reads should be replaced by helper methods:

```rust
computation.effect_var_for_semantic_slot(...)
computation.effect_flow()
self.connect_effect_flow_to_var(flow, target)
self.connect_pos_to_effect_flow(pos, flow)
self.materialize_effect_flow(flow, reason)
```

The compatibility `effect` field should shrink over time. It should not be used
for newly introduced administrative joins.

## Phase 0: Diagnostics Before Refactor

Add temporary diagnostics behind environment variables, not default output.

Required traces:

- each fresh subtract id with source location;
- each administrative effect join creation;
- each `EffectFlow` materialization reason;
- each var-var pop replay key hit;
- origin contour for any nonzero displacement SCC after administrative ports
  are ignored.

Suggested flags:

```text
YULANG_TRACE_EFFECT_FLOW=1
YULANG_TRACE_ADMIN_JOINS=1
YULANG_TRACE_VAR_VAR_REPLAY_KEYS=1
```

Stop condition:

- Trace output shows a semantic variable is being classified as administrative.
  Do not continue the refactor until the classification is fixed.

## Phase 1: Flow Facade With No Behavior Change

Goal: introduce types and helper methods while preserving current constraints.

Steps:

1. Add `EffectFlowId` and a small `EffectFlowTable` in lowering.
2. Give every existing `Computation` a flow that is initially just
   `EffectFlow::Var(effect)`.
3. Add helper methods:
   - `effect_flow_var(effect)`;
   - `effect_flow_pos(pos)`;
   - `seq_effect_flows(parts)`;
   - `connect_effect_flow_to_var(flow, var)`;
   - `connect_pos_to_effect_flow(pos, flow)`;
   - `materialize_effect_flow(flow, reason)`.
4. Replace obvious direct `subtype_var_to_var(x.effect, target)` calls with the
   helper, but make the helper emit the same constraints as today.

This phase should be a pure refactor.

Validation:

- `cargo test -q -p infer lowering::tests::case_04::std_ref_update_method_body_lowers`
- `cargo test -q -p infer lowering::tests::case_03::dollar_binding_lowers_to_var_ref_and_run_wrapper`
- `cargo test -q -p infer -- --test-threads=1`

Stop condition:

- Any scheme rendering changes. Phase 1 is not allowed to change behavior.

## Phase 2: Block / Tuple Administrative Sequencing

Start with the purest administrative joins.

Targets:

- `crates/infer/src/lowering/expr/block_local.rs::prepend_block`
- tuple/record/list/rule-literal sequencing where effect joins only collect
  sub-expression effects.

Change:

```text
head.effect <: fresh
tail.effect <: fresh
```

to:

```text
Seq(head.flow, tail.flow)
```

The returned `Computation` should carry the `Seq` flow. Materialize only when a
later semantic consumer requires a `TypeVar`.

Important:

- Do not remove semantic effect variables for values that are part of a
  generalized type.
- Keep `Evaluation` logic unchanged. Effect flow and value restriction are
  separate.

Validation:

- Existing block/case/catch lowering tests.
- Add a regression where a recursive callback passes through a block before the
  lambda predicate boundary.

Expected result:

- No principal scheme changes except where an administrative variable was
  previously visible only through an internal dump.

## Phase 3: Application Result Flow

Target:

- `crates/infer/src/lowering/expr/tail.rs::make_app`

Current critical edges:

```rust
self.subtype_var_to_var(callee.effect, result_effect);
self.subtype_pos_to_var(return_effect.lower, result_effect);
```

Change the returned effect to:

```text
Seq(callee.flow, Pos(return_effect.lower))
```

where `return_effect.lower` still contains the `push(Empty)` wrapper for
unannotated local callees.

Do not alter:

- `unannotated_local_callee_return_effect`;
- `StackWeight::push(subtract, Empty)`;
- matching predicate `pop` registration in the function frame.

Validation:

- `std_ref_update_method_body_lowers` must keep:

  ```text
  ('b -> ['c#4[Empty]] 'b) -> ['c#4(1)[Empty], 'a#4] ()
  ```

- The broad `(lower, upper)` no-op experiment must remain unnecessary and
  rejected.

Stop condition:

- If `#4[Empty]` disappears, the flow connected the producer to the wrong
  consumer or materialized too early.

## Phase 4: Defined Lambda Skeleton Hole

Targets:

- `fresh_defined_lambda_skeleton`
- `connect_defined_lambda_skeleton_predicates`
- `lower_defined_lambda_params`

Current issue:

```rust
body.effect <: skeleton.body_effect
body.value  <: skeleton.body_value
```

creates a replay-visible alias proxy before the predicate pop is applied.

Plan:

1. Replace `DefinedLambdaSkeleton.body_effect: TypeVar` with a flow hole.
2. Before lowering the body, register predicate consumers on that hole.
3. While lowering discovers late unannotated callback subtracts, refresh the
   hole consumers instead of adding a new ordinary alias path.
4. After body lowering, fill the hole with `body.effect_flow`.
5. Keep `body_value` as a normal `TypeVar`; the problem is effect sequencing,
   not value unification.

Required behavior:

- The skeleton is available before the body so recursive references still see a
  stable function shape.
- Late callback subtracts still update the skeleton output.
- No ordinary `body.effect <: skeleton.body_effect` edge is emitted solely for
  sequencing.

Validation:

- recursive defined lambda tests;
- late unannotated callback subtract tests;
- multi-argument/curry defined lambda tests;
- `std_ref_update_method_body_lowers`.

Stop condition:

- If recursive references instantiate a fresh scheme inside RHS, stop. The
  monomorphic root invariant must not be touched.

## Phase 5: Catch Flow

Targets:

- `crates/infer/src/lowering/control.rs::lower_catch_with_scrutinee`
- `subtype_scrutinee_effect_to_row`
- `lower_catch_arm`

Current pattern:

```text
arm.body.effect <: result_effect
scrutinee.effect <: result_effect / row boundary
```

Plan:

1. Represent handler result as:

   ```text
   Seq(residual_tail_flow, effect_arm_flows, value_arm_flow)
   ```

2. Connect the scrutinee flow directly to:
   - handled row boundary;
   - incomplete-handler passthrough consumer;
   - public effect slot where needed.
3. Keep `LocalEffect::Stack` as the source of subtraction hygiene, but avoid
   duplicating the same provenance as independent replay paths.

Validation:

- complete/incomplete catch tests;
- shallow continuation tests;
- annotated recursive handler tests;
- `std_ref_update_method_body_lowers`.

Stop condition:

- If handler residual tails stop appearing in principal schemes, the residual
  tail was accidentally treated as administrative. It must remain semantic.

## Phase 6: Materialization Boundaries

After the main lowering paths use flow, audit all remaining `.effect` reads.

Allowed materialization points:

- connecting a computation to an annotation whose result must be a semantic row
  variable;
- generalization/compact boundaries;
- public scheme roots;
- runtime IR places that need a concrete effect slot for later passes.

Suspicious materialization points:

- block result;
- application result;
- catch result;
- defined skeleton body proxy;
- tuple/record/list effect aggregation;
- temporary hidden wrappers.

Every materialization should carry a short reason enum, not a raw helper call.

## Phase 7: Remove The Temporary Replay Key

Only after flow migration:

1. Add a diagnostic that counts var-var pop replay key hits.
2. Run the regression suite.
3. Confirm the key hit count is zero for source-generated tests.
4. Remove `var_var_pop_replay_seen`.
5. Keep exact `seen` keys with full labels.

If key hits remain:

- dump the origin contour;
- classify whether it is a missed administrative join or a real semantic cycle;
- do not remove the key until the source is understood.

## Regression Matrix

Must pass after each phase:

```text
cargo fmt --check
git diff --check
cargo test -q -p poly
cargo test -q -p infer lowering::tests::case_04::std_ref_update_method_body_lowers -- --test-threads=1
cargo test -q -p infer lowering::tests::case_03::dollar_binding_lowers_to_var_ref_and_run_wrapper -- --test-threads=1
cargo test -q -p infer -- --test-threads=1
```

Add focused regressions:

- block between callback call result and defined lambda predicate;
- catch arm between callback call result and defined lambda predicate;
- recursive handler with annotated argument and unannotated callback;
- multi-layer defined lambda where a late callback subtract appears in an inner
  layer;
- effect flow diagnostic test where administrative ports are absent from the
  replay graph;
- structural SCC test proving all source-generated cycles have displacement
  zero after administrative flow removal.

## Commit Strategy

Keep commits small:

1. Flow facade, no behavior change.
2. Block sequencing.
3. Application sequencing.
4. Defined skeleton hole.
5. Catch sequencing.
6. Diagnostics and replay-key removal.
7. Spec/research cleanup.

Do not mix a behavior change with a large mechanical `.effect` helper rewrite.

## Open Questions

- Should `EffectFlow` live in `typing.rs` next to `Computation`, or only inside
  lowering? Start inside lowering if possible; move to `typing.rs` only when the
  public `Computation` API must expose it.
- Can catch passthrough be represented as a consumer on the scrutinee flow
  without duplicating the `LocalEffect::Stack` provenance?
- Does compact/generalize need to know about flow origins, or can every flow be
  fully emitted before those phases?
- Should the final proof mention `EffectFlow` explicitly, or keep it as the
  implementation of the existing fan-out normalization lemma?

## Success Criteria

The refactor is complete when:

- `std_ref_update_method_body_lowers` keeps its exact marker-bearing scheme;
- var-var pop replay key diagnostics do not fire on source-generated tests;
- removing the temporary count-less replay key leaves `infer` green;
- the proof no longer needs an implementation caveat for fresh effect joins;
- no direct `.effect` join is introduced for sequencing without an explicit
  materialization reason.
