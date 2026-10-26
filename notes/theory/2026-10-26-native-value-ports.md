# Constructed native Value ports and ordered child dispatch

Date: 2026-10-26. Author: primary `/root`.
Baseline: `8472a1ca49da055a1ea298ccfa87745c2a6f5ce4`, `yulang3`.
Status: frozen mathematical construction, awaiting fresh independent review.

## 1. Original owner and claim

The original parent remains full native inference correspondence and, through the
same original scoped witness, `SourceProblem.InferenceSoundness`. The immediate
missing owner is structured Value dispatch after the Context stage. The accepted
[Context construction](2026-10-26-native-context-expansion-construction.md) forwards
an intact `ValueRequest`; it does not construct the children of a Function, Tuple,
Record or Variant. This packet constructs those children's complete keys and the
actual two-stage admission/enqueue sequence.

The implementation owners are `crates/yu-solver/src/lib.rs` lines 14432–14869
(`dispatch_live_item`), 14955–15054 (the four child steppers), and
`crates/yu-solver/src/candidate_context.rs` lines 2630–2656 (Context interning),
2795 onward (scope interning), 3062 onward (relation guards/interning), 3349–3376
(canonical/source-local Context), and 3511–3669 (the four port admissions).
The transformer constructors/evaluation are in `candidate_scope.rs` lines 97–125
and 180–216. The exact source snapshots and hashes are retained in the handoff.

`NativeValuePorts.lean` imports the frozen Context construction and existing
`NativeRecordPlan`. It changes no solver, expected output, supported syntax,
production configuration or checker policy.

## 2. Complete data and construction

`ValueEndpoint` retains every native endpoint constructor, including polarity,
Function/Record/Variant term identity and Tuple arity. `Pair` distinguishes Value
from Effect. Canonicalization renames only native row identities. The full `Key`
contains that pair, Context ID, optional source-set ID, and `Flow`. Flow retains
its transformer ID and the entire five-field `ScopedDemand`: original Call,
use instance, root, output scope and input route. No endpoint-only memo replaces
this key.

`Port` preserves the actual Function field, Tuple index, Record lower/upper
indices, or Variant lower/upper/payload indices. A `Receipt` retains its entire
parent key, constructed child key, relation ID, exact port and the additional
Derived flag. `Receipt.dependencies` always includes the typed port dependency;
Derived is additional. The Function `Swap`/`Preserve` choice is determined by
`Port.swaps` from that same field.

The chronological `intern` function compares the whole object, reuses its existing
index or appends it. `intern_found`, `intern_extends` and `intern_reuse_exact` prove
readback, all old meanings and that sequentially reusing an index implies equality
of the complete objects. `Arena` contains Context nodes, complete transformer
records and decoded complete relation keys. These are mathematical raw table
payloads, not original semantic descriptor witnesses.

## 3. Context order and native input formation

`buildContext` performs the native order:

1. Intern the child-local `PrefixLeft(weight, Identity)`, when present.
2. For Argument/ArgumentEffect, wrap the supplied actual post-check Context in
   `Swap`, except that Identity remains Identity.
3. Put the child-local prefix outside the inherited Context operation.

The input is the actual post-check Context ID, not a silently substituted stored
parent Context. `sourceWeight` distinguishes a missing table view from an existing
view without a closed weight. Only an Effect upper Allowance supplies such a
prefix; Value tasks do not.

`build_context_exact` constructs the intermediate ID and actual stored node
lookups, and `build_context_extends` keeps every prior arena meaning. The native
`context` constructor asserts that its input IDs already exist. `ContextsFormed`
therefore uses the exact earlier-ID condition, and `build_context_formed` proves
that a formed input arena and valid supplied post-check ID produce a formed arena
and valid result ID. This is a raw structural premise, not typing or body safety.
The concrete example starts with the existing `WithoutLeftFilter(Identity)` at
ID 1; it does not use an unallocated post-check ID.

## 4. Full deferred demand and Function effects

Tuple, Record and Variant admission preserve the whole parent Flow, including all
five demand fields. Function admission first requires identity incoming transformer.
For a deferred demand it checks that the actual parent's upper endpoint is the
negative Function rooted at that exact demand root, and consumes the demand once.

The Value Argument and Result children receive identity flow. ArgumentEffect
constructs `stamp_input(demand.inputRoute)`; ResultEffect constructs
`protect_body(demand.outputScope, demand.inputRoute)`. These are actual finite
transformer records, interned in the same output arena. The parent retained by the
port dependency still contains the original Call/use/root identity.

The checked pointwise meanings of these exact new transformers are:

- stamp adds precisely the input route, preserving all protection membership;
- protect keeps the input routes, retains old protection, and adds the selected
  output scope exactly when the original input route is absent;
- every different scope keeps its old membership.

No effect members or capture grants are synthesized by these operations.
`build_flow_exact`, `argument_effect_scope`, `result_effect_scope` and
`structural_demand_preserved` expose these facts. `Allowed` retains the native
Value/nonidentity-transformer rejection, Effect/deferred-demand rejection, and
nonidentity Effect self-relation rejection.

`admit_constructs` starts with actual computed `admit = some (arena, receipt)` and
constructs all parts of `AdmissionResult`: exact pair, sources, parent, port,
Derived flag, Context nodes/order, complete Flow meaning, guards and registered
full child key. Old Context/transformer/relation readbacks remain valid in that
same resulting arena. There is no semantic child-typing or completed-owner premise.

## 5. Actual structured child lists

`functionChildren` constructs the original four ordered fields from one pair of
complete raw Function term tuples. Argument and ArgumentEffect are contravariant;
ResultEffect and Result are covariant. `TermEndpoints` are fixed native store
readback functions for those term IDs, not comparison or safety predicates.

`tupleChildren` checks both advertised arities and both actual vector lengths,
then computes every paired child with its exact original index. The theorem
proves the resulting length and every corresponding element.

`recordChildren` uses the existing checked first-name native scan. It retains
absent optional slots, required-field diagnostics, optional-to-required
unavailability, source duplicate handling and original target positions. Its
successful output maps all actual holes to Record ports. Failure publishes no
partial child vector. The witness with an absent optional target followed by a
required target produces Record indices `(0,1)`, not `(0,0)`.

`variantChildren` checks each positive alternative against all negative entries
with the same tag and payload count, preserving lower/upper alternative indices
and every payload position. Equal negative keys are not deduplicated. The generic
no-omission theorem covers all matching requirements; `variant_first_missing`
identifies the first missing lower alternative and discards the earlier prefix.
`Except.error` here denotes that native diagnostic outcome, not a claim of Rust
availability failure. The concrete duplicate-key witness produces two different
payload comparisons from one positive alternative.

## 6. Two-stage execution and one source order

A `Cursor` retains the immutable child's reverse traversal, completed prefix,
pending admitted receipt, actual front-enqueue queue and same arena. Its native
`next` cursor is the completed prefix length. Admission computes `admit` and stores
the pending receipt before enqueue. Enqueue uses that same receipt, retains the
original raw task even if its canonical child key differs, clears pending, advances
one position, and pushes to the front. No Replay acknowledgement is fabricated.

`dispatch_step_valid` and `dispatch_run_valid` prove one common invariant:

- completed prefix plus remaining children equals the original reverse vector;
- completed receipts correspond exactly to that prefix;
- the queue is the reverse of those actual completed jobs followed by its old tail;
- every completed or pending receipt has its constructed complete key in the same
  current arena, including old receipt meanings after later allocations.

`next_source_index` derives the exact native array access. `finished_pending_none`
derives that end-of-vector leaves no unqueued admitted item; this is a conclusion,
not an extra success assumption.

`drive` executes these real two stages with a proof-side finite step counter.
`drive_constructs_run` constructs the step history from the computed result.
`drive_success_readback` starts only from this actual successful computation and
returns one complete list of jobs in original source order, exact queue equality,
every full `AdmissionResult` and absence of Replay acknowledgements. No new source
or native time limit is imposed by the proof-side fuel.

The checked Function witness computes all eight admission/enqueue steps for four
ports from an existing parent and formed Context arena. It retains the same source
set and original deferred Call/use/root throughout the constructed dependencies.

## 7. Exact remaining parent boundaries

This is an allocation-success mathematical transcription of selected native
constructors, not a verification of the Rust binary. The Arena stores decoded
complete relation keys; the native ScopedFlowId hash interner and its enabled flag,
capacity/inventory checks, allocator failures, index overflow and error-path partial
mutations still need their actual refinement. Successful native entry supplies the
parent lookup, raw table/term lookups and formed input Context; their authenticity
is not inferred from arbitrary mathematical arguments. Formation is separately
proved above, not claimed for arbitrary malformed arenas.

The packet does not prove all branches of `dispatch_live_item`: current-memo reuse,
canonical or retained extrusion rewrites, incompatible-shape diagnostics, bottom/top
shortcuts, fallback row propagation and merge/extrusion events retain their owners.
The new structured port constructor can supply child data to those native history
proofs, but does not turn `record_typed_pair_admission` into a completed body.

The shared Context/drain lane must connect these constructed children and their
pending enqueue stage to actual issued occurrences, completed bodies, diagnostic
acceptance, merge/cancellation/versioned table history and terminal Replay receipts.
The original source lane still must construct the entire original `nu,K,D,eta0`
interpretation, full descriptor/Call/method/annotation meaning and all independent
challenges. Four signed scalar Function ports alone do not establish a complete
original callable contract. No whole inference, termination, principality or
production promotion is asserted here.

## 8. Verification record

Pinned Lean 4.35.0 / commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The isolated `value-ports-r4/project` contains the exact published checkpoint-4
sources; none of the concurrently changing source/Context-readback files is an
input. The final helper checks all **56 authored roots**, and the complete origin
audit checks **891 declarations / 348 theorem constants**, including generated and
private declarations. The theorem axiom census is **235 none, 88 only propext,
25 propext plus Quot.sound**. No Classical.choice, project axiom, sorryAx, native
evaluation axiom or kernel bypass appears.

Final calls 12 (module plus all roots) and 13 (full origin census) exit zero.
Thirteen of twenty allowed calls were consumed. Failed scripts and source snapshots
remain preserved; none is represented as successful evidence. Lean stays at `-j1
-M1024`; the wrapper+Lake aggregate ceiling is 1280 MiB, as already justified for
this toolchain. The audit prints full proof-bearing types, drains UTF-8 output to
EOF and checks balanced inventory/trailer/root coverage. The primary's first
read-only census parser was interrupted for a greedy expression, then repaired
without changing the Lean log; that parser incident is separately retained.

The full types, standard axioms, commands, hashes, source mapping and precise
remaining obligations are in the accompanying inbox. Fresh independent review is
required before integration; the primary cannot independently accept its own proof.
