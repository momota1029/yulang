# F5c depth-bounded boxed-draft stack-safety subgate

Status: Reviewed; pending explicit user approval
Scope: native-stack safety of F5c boxed draft construction, finalization, and destruction
Related authority: F5 §§14, 24–26, 32–36, 43–44; F5b closed-finalization accounting amendment §§2, 6, 9
Reviewed-by: spec_auditor and performance_auditor; focused M2 delta review, 2026-09-24
Decision: pending approval of maximum structural depth 128 and `IdentityExhausted` rejection above it
Supersedes: none; proposes to specify the over-limit outcome for F5 §14's deep-chain stack-safety requirement

## 1. Problem and product direction

F5c builds recursively owned `F5cPositive`/`F5cNegative` trees in iterative
worklists. The unchanged §24 finalizer then recursively visits those trees, and
ordinary success/error cleanup recursively drops them. Thus iterative
construction alone does not prevent stack overflow.

The user's 2026-09-24 product direction prioritizes Oracle-equivalent results
on practical inputs and a lightweight successful path. Pathologically deep
inputs may be rejected deterministically while accepted-input invariants and
atomic public publication remain intact. This reviewed proposal covers only
the stack-safety subgate: retain the current boxed representation and §24
callback, and reject excessive structural depth before constructing an
over-limit parent. It does not authorize implementation.

## 2. Proposed supported depth and failure behavior

For F5c boxed values, define structural depth using the existing
`Normalizer::Node.height` measure:

- a leaf has height zero;
- each constructed Function, Union, or Intersection adds one above its deepest
  child;
- an alias/shared reference that emits no parent node adds no depth.

Proposed maximum depth: **128**. Before constructing/attaching every parent,
check `1 + max(child_depths)` with checked arithmetic. If that would exceed 128,
return the existing `SolveAvailabilityError::IdentityExhausted`. A depth-129
source can have its bounded children traversed, but the depth-129 parent is
never boxed or published to a worklist. No public error variant is added.

This is a proposed input boundary, not a measured stack guarantee. Before this
subgate is called complete, tests must show both polarities at depth 128 can
normalize, pass the unchanged §24 finalizer, and be normally destroyed on a
64 KiB thread stack. Checked-error cleanup must also drop safely at that depth.
Depth 129 must fail before its parent is built, and the already-built depth-128
children must safely drop. If any proof fails, lower the limit and return to
review, or use a flat/indexed ownership design; do not rely on a larger host
stack.

On any solver error, consuming `InferenceSession::run(self)` returns without a
`SolvedModule`. Within a component, all plans are normalized/finalized before
that component's separate scheme-install loop. This says nothing about private
staged arena bytes or schemes installed for earlier components; the session is
consumed and no partial `SolvedModule` is returned.

## 3. Required enforcement and cleanup invariant

Carry depth as private sidecar metadata in iterative value stacks. Do not add a
recursive depth rescan or a public solver/`yu-types` API. Every production
boxed-value producer must check before attaching a parent or placing it in an
output stack. The inductive invariant is: leaves have depth zero; each
parent's checked prospective depth is one plus its deepest child; no parent is
constructed unless that value is at most 128. Thus a checked failure after
children have been removed from a task/value lane can only recursively drop
children already bounded by 128, never an over-limit partial parent. If an
error occurs after a bounded parent is formed, that parent is likewise safe to
drop. The small-stack failure-cleanup test below must validate this argument
for the actual representation.

- `F5cGeneralizer::walk`: Function exits and normalized Union/Intersection
  exits;
- `F5cComponentExpansionMemo::materialize_summary`, including repeated shared
  occurrences;
- `f5c_materialization`, `f5c_replay`, and
  `f5c_binder_substitution`: Function and product exits;
- predicate and recursive-bound materialization;
- `Normalizer::push_node_at`: enforce the already-computed `Node.height` before
  appending a flat parent node. This uses the existing child-height pass; do
  not add a whole-node rescan. `push_node` may already have copied child IDs
  into flat scratch and grown that lane before the height check; rejection does
  not promise zero work or allocation on the failure path. Keep a local check
  before each boxed parent in `Normalizer::rebuild` as a defense-in-depth
  invariant.

The bound must hold at every ownership transfer into raw bounds,
`GeneralizationDraft`, replay/substitution output, normalized drafts, and all
partial task/value stacks. Error cleanup may recursively drop remaining boxes
only because every earlier producer checked its parent before construction;
there can be no over-depth partial tree to drop. In normalization, an
over-limit height is rejected as each flat parent node is computed, before it
is appended or any output tree is rebuilt. A later non-depth error during
rebuild may leave partially rebuilt values, but each parent was independently
checked and is therefore bounded. Review must trace every production
`Box::new` and product `Vec` constructor; an uncovered producer or clone
invalidates the proof. Current producer inventory to verify includes
`F5cComponentExpansionMemo::materialize_summary`, `F5cGeneralizer::walk`,
`f5c_materialization`, `f5c_replay`, `f5c_binder_substitution`, and
`Normalizer::rebuild`, including predicate and recursive-bound outputs.

Input `Term` values are arena handles, not recursively owned children, so a
depth rejection while walking them does not recursively drop a deep source
Term. Production recursive clones of F5c trees are not permitted unless they
preserve the same guard; the current replay leaf clone is not a recursive-tree
clone.

## 4. Preserved properties and explicit residuals

For inputs at depth at most 128 that otherwise complete successfully, preserve:

- exact F5c polarity, Q/R classification, and binder order;
- normalized first-member Union representative and private-member routing under
  §44;
- current §24 finalization API and `run` return contract (an error returns no
  `SolvedModule`), without claiming rollback of private session state;
- iterative construction and current normalization order.

The new observable behavior is that a component exceeding depth 128 returns
`IdentityExhausted` instead of continuing to build a deeper scheme. It is not
truncated or approximated. This proposes a narrow clarification of F5 §14's
sentence, “Generalization uses an iterative worklist; it must not recursively
overflow on deep chains.” The proposed addition would define the supported
structural depth as 128 and require deterministic `IdentityExhausted`
rejection before an over-limit parent is built, so accepted chains stay within
the tested stack bound and excessive depth cannot reach recursive finalization
or destruction. No other F5 asymptotic or semantic clause is proposed for
supersession.

This subgate does **not** bound shallow width, repeated shared-summary
expansion, aggregate component work, or total memory. A sufficiently wide or
amplified shallow input may still consume substantial memory; that separate
F5c construction/resource gate and F5e resource/public-observation
certification remain open. Do not claim general resource protection or F5c/F5e
closure from this stack-safety slice.

The successful path gains only sidecar depth propagation and a checked bound
at existing parent-construction points; no whole-tree rescan, global work
counter, per-lane cap, or new allocation owner is proposed. The sidecar's
actual slot-size impact must be read from `size_of::<F5cWalkValue>()` and remain
visible to the existing walker-lane accounting.

## 5. Review and implementation gate

Review result: the focused M2 spec and performance delta reviews completed on
2026-09-24 with no blocking or major findings. The performance review's minor
failure-path allocation note is recorded in §3.

Implementation remains gated on recording the user's explicit approval of the
depth-128 rejection boundary and `IdentityExhausted` behavior.

After approval, implementation verification must cover both polarities,
every production tree producer, normalized output, depth-128 successful
finalization/destruction on a 64 KiB stack, depth-128 checked-error cleanup,
depth-129 rejection before parent construction, and a failing solve that
returns no `SolvedModule`. The latter does not assert rollback of private
session state. The existing
`f5c_deep_alternating_function_walk_and_comparison_are_iterative` test uses
depth 2,048 and currently asserts successful construction; other synthetic
2,048/4,096-depth helper tests may assert the same kind of success. These
expectations and test names are outside the proposed boundary and must remain
unchanged until the user approves it; then update only the witnesses whose
contract genuinely changes. Do not describe the resulting gate as supporting
arbitrary depth. Run focused checks first, then the single-threaded
`yu-solver` library suite once at the coherent gate boundary. These are stack
safety tests, not timing benchmarks.

No implementation, API, or Authoritative F5 text has changed; depth 128 remains
a proposal pending the user's approval.
