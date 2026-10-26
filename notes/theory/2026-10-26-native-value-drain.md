# Constructed native Value issuance and one drain history

Date: 2026-10-26. Author: primary `/root`.
Initial baseline: `82b8fb669c5b51c6c99771cd2208c9730ebc85c3`, `yulang3`.
Status: construction frozen for fresh independent review; the original parent is OPEN.

## Original owner and exact contribution

The parent is the original full native correspondence and
`SourceProblem.InferenceSoundness`, with the same original scoped witness.
`NativeValuePorts` constructs the full structural children and their two-stage
admission/enqueue execution. `NativeDrainOwnership` proves ownership and return
coverage in an actual drain-control history. The missing connection was the
construction of those control occurrences from that very child execution; two
independently assumed histories would not establish it.

`NativeValueDrain` constructs both projections together. The actual native
preflight, the original computed outer structural branch, the existing port
admission computation, the immutable control occurrences and every ensuing
quiescent return now occur in one constructed prefix and its continuation.
No conclusion here asserts that a diagnosed return is conflict-free, that a
finite quiescent continuation exists, or that every returned body satisfies the
original source semantics.

The native owners are `crates/yu-solver/src/lib.rs`: the top-frame preparation
and acknowledgement cursor at 14261–14287, dispatch at 14432–14869, and the
Function/Tuple/Record/Variant steppers at 14955–15054. Their port admission
constructors are in `candidate_context.rs` at 3511–3669. The exact immutable
control transition correspondence is the already reviewed
[drain ownership construction](2026-10-26-native-drain-ownership.md).
The complete decoded key and raw port correspondence is the reviewed
[Value port construction](2026-10-26-native-value-ports.md). The separately
published and reviewed
[outer Value construction](2026-10-26-native-value-structure-r5.md) is pinned at
`e5d2b7b7a6ec340743668075780e95e8a98c8ef5`, rather than read from a moving worker.

## Actual preflight, including commit and re-preparation

Every native structural step calls `prepare_nonterminal_drain`. It checks the
actual top frame index and `completed <= prepared <= acknowledgements.len`,
records the undo state, and prepares every as-yet-unprepared acknowledgement.
A later commit re-arms that cursor. Treating the whole frame as unchanged from
an arbitrary raw active input would therefore have been an incorrect native
correspondence, even though the enqueue-only algebra itself is valid.

`prepareOne` reads the actual top frame, selected ticket, owning replay operation,
consumed/queued bounds and exact completion wait state. It computes the update
of only `prepared`; `prepare_one_step` constructs the corresponding
`NativeDrainOwnership.Step.prepare`. `prepareAll` executes those real steps with
finite proof-side fuel. `prepare_all_exact` constructs their common Run, derives
the completed preparation guard, and identifies the exact final frame update.
It preserves every other control field.

The raw parent premise `ParentPresent` is the actual top working frame, immutable
current occurrence, separately selected processing relation, and lookup of the
whole parent key in the input arena. It does not identify the admitted relation
with the processing relation: transport may have changed the latter.
`preflight_parent_active` obtains the prepared parent from the actual computed
preflight, rather than requiring a preprepared input. After preparation the
plain structural builder adds no replay acknowledgement; the theorem
`emission_preparation_stays_complete` proves that every repeated native preflight
inside that builder is a stutter. The commit witness uses the actual control
commit transition and reconstructs preparation of the already existing ticket.

This is the allocation-success control projection. Native undo-vector reservation,
allocator failures and checked integer/capacity guards retain their implementation
owners. Successful proof-side computation is not a claim that allocation always
succeeds. The preflight fuel is not a new source-language or native runtime limit.

## One occurrence at the real enqueue event

`State` pairs the existing port cursor with the complete drain `Control`, a ghost
raw-task naming table and the chronological issuance records. The cursor queue
records only the newly constructed child prefix. Its control component retains
an arbitrary old native queue; no premise requires that old queue to be empty,
plain, decoded by this task table, or independently synchronized with the cursor.

Admission computes the existing full `admit`, stores its pending receipt and
stutters the control state. Enqueue consumes that same pending receipt, interns
the complete original raw task in a ghost naming table, reads the ghost occurrence
counter `Control.nextWork`, creates the immutable occurrence and front-enqueues it through
`NativeDrainOwnership.pushWork`. The cursor update, issuance record and control
update are one event. This ghost table names the existing whole native payload;
it does not assert an additional native allocation or erase Value/Effect polarity.
The serial counter and issued/returned occurrence history are proof annotations
attached to real control events, not fields stored by the Rust implementation.

Each `Issuance` keeps the entire port work and the entire native occurrence.
`Issuance.matches` checks the whole raw task lookup, admitted full relation and
absence of a replay ticket. The record retains the actual port, parent key,
child key, demand, source-set and post-check Context through the original
`AdmissionResult`. The active parent is interpreted by processing relation,
separately from the occurrence's immutable original admitted identity.

`step_control` and `run_control` derive the actual control transitions from this
history. `step_cursor` and `run_cursor` derive the existing port dispatch history
from the same events. No independently supplied matching middle state appears.
The joint invariant derives all of the following together:

- full cursor validity and the original reversed traversal;
- exact one-to-one correspondence between issuance records and cursor records;
- every full raw task/receipt/occurrence association;
- exact old issued list plus the chronological new occurrences;
- exact reverse-issued front queue followed by the arbitrary old queue;
- the actual next serial and the contiguous serial range of those occurrences;
- preservation of the prepared frame during this structural builder;
- extension of raw task names and every complete arena readback.

`emit` is executable construction of both states. `emit_cursor_exact` proves
that its cursor projection is exactly the existing `NativeValuePorts.drive`.
Consequently `native_drive_constructs_common_run` starts from the actual successful
port computation and constructs the control state and history; their agreement
is proved, not included as an input requirement.

## Returned child coverage and direct outer composition

`completed_issuance` obtains one list in original source order, the exact queue
and issued-list equations, the absence of pending admission, and every full child
admission receipt in the same output arena. The concrete four-port witness starts
from an actual begin/take parent prefix and the existing formed arena. It computes
serials `[1,2,3,4]` in issuance order, native queue `[4,3,2,1]`, next serial 5, and
no transferred replay work.

`emitted_children_returned` composes the actual initial prefix, the constructed
emitter Run and a continuation starting at precisely its computed control state.
If that continuation ends with an empty queue and frame stack, every generated
child belongs to a recorded returned frame with diagnosis executed, ReturnReady
phase, no pending child and no current work. This is the accepted quiescent
coverage theorem applied to those very issued occurrences. It does not infer
successful diagnostics from the `diagnosed` bit or replace body semantics with
that control certificate.

`native_children_pipeline` removes the prepared-frame assumption: its inputs are
the raw current parent, actual preflight result and actual port-drive result.
It constructs the middle state and all future quiescent return conclusions.
`context_execution_native_drive` extracts the exact child vector and drive equation
from the computed `NativeValueStructure.executeAfterContext`. The final root
`context_value_pipeline` composes these constructors. The resulting child list is
chosen by the actual outer Function/Tuple/Record/Variant branch, not an input
asserted to match it. It also derives identity incoming transformer, candidate
mode, full unchanged parent key, the same output cursor and the same drain Run.
The irrelevant incoming `Origin.children` field is replaced by that computed list.

This adapter covers the represented structured candidate branch. Other native
branches remain represented by their existing owners; a failure/None in this
adapter does not remove those branches from the language or original theorem.

## Original parent boundaries that remain

The proof closes the independent-child-history gap for these computed structural
branches. It still requires authentication of the raw memo/current/retained,
canonical row, term/endpoint, post-check Context, scope and relation-arena inputs
in one committed native history. The published outer dispatch explicitly treats
these as observed inputs. Their physical ScopedFlowId interning, allocation and
error behavior are not replaced with arbitrary mathematical raw arguments.

The already active Context table lifetime owner supplies versioned table
allocation, publication, cancellation and retry readback. The Context callback
owner constructs its own actual queue occurrences. Neither independent construction
by itself authenticates every Value/Effect rewrite, row merge/extrusion, bound
insertion, replay or diagnostic publication. Their common committed native history
and complete body semantics still require composition with their actual owners.

Original Function/Call, name/dictionary, annotation, instance, record-adaptation,
primitive/State/effect semantics, all source constructors and the same scoped
semantic witness remain required. The root `SourceProblem.InferenceSoundness`,
principality, solver termination and production promotion are not closed here.
No solver, supported syntax, expected result, toolchain or configuration changed.
The exact theorem inventory, commands, failures, hashes and complete originating
theorem types are retained in the accompanying author handoff.
