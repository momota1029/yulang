# Record plans: finite prefixes, requests and reusable responses

Status: checked research component; independent review pending.
Baseline: `b26e7de1aada0e15ac5147feb8654ec34ac90275` (`yulang3`).
Implementation: `lean/YulangClosure/RecordBoundaryExecution.lean`.

## Original obligation and precise advance

The original whole-language inference-soundness target is unchanged. The local
source is the record-boundary section of
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex`, especially the
ordered ordinary-bind rule and record preservation theorem at lines 378–403.
Its fixed SHA-256 is
`28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
This manuscript remains a research specification, not production adoption.

`RecordBoundaryPreservation` previously proved normal-result typing and exact
visible-field survival from a normal child-run relation. It did not represent
requests, pending computation or resumption. The new component constructs the
ordinary bind driver and its invariant, proving the corresponding compositional
finite-prefix contract from independently supplied child-computation contracts.
It does not supply those child contracts from native inference, reconstruct an
authentic source adaptation boundary, or prove full contextual Call meaning.

## Independent payload contract

`Observation Child Value Request Response Failure` is one layer of an arbitrary
payload machine: internal successor, returned value, request plus response
continuation, or explicit failure. The state is arbitrary; it may contain cycles,
so the representation does not restrict computations to finite trees.

For fixed independent value typing, request admissibility and response typing,
`Safe depth state` checks every observation up to that depth. Depth zero is the
unconditional zero-step prefix. A request requires the original packet to be
admissible and every typed response to continue at the next smaller depth.
`SafeAll` quantifies over every natural depth. Explicit failure is a permitted
exit and does not produce a normally typed result. The failure tag is retained.
No termination, eventual response, finite request count or finite branching
hypothesis is introduced.

`ChildrenSafe` says that an actual resolver-selected child, started on an
independently typed payload, meets this contract at its target payload type.
It contains no record-state invariant or record-safety conclusion. The manuscript
itself requires independent child contracts; the new proof discharges their
composition, not their production. The theorem quantifies over arbitrary request
and response types, which can retain complete packet records. This is still a
fixed local contract: interpreting it as the original provider/world/guard
envelope, and establishing current-world validity of retained values, remain
separate source/child obligations.

## Executable ordered record composition

The record driver has two states: scanning the unprocessed plan with the
completed output prefix, and running a child while retaining its field, output
prefix and pending plan. It consults only the original visible input map and the
raw child observation. No transition takes a typing proof.

An absent target emits an absent slot. A common field reads the visible input:
an absent input remains absent, while a present input starts the retained cast.
When that child returns, its value fills the same field and scanning continues.
Internal child steps leave the record frame unchanged. A child request exposes
exactly its original packet; the saved response function reinstalls the identical
output prefix, field and pending plan around the resumed child. Failure returns
the original failure tag and does not scan later fields. No backing-object lookup,
default evaluation or field resurrection is introduced.

`StateTyped` retains a partition of the original target list, an independently
typed and visibility-correct completed prefix, the original valid pending plan,
and the active child's contract when present. `state_closed` constructs the
invariant for every possible raw observation. Its proof handles absent optional
fields, actual required presence, child steps, returns, requests and failures.
`state_transition_preservation` and `compiled_trace_invariant` apply this result
through any finite actual path, including any number of typed resumptions.

The output predicate `OutputsGood` retains target order, label correspondence,
every present payload's declared type and exact input-presence equality per slot.
It implies the existing `OutputTyped` predicate. The final map therefore has
precisely the intersection of the original visible labels and target labels.

The driver uses list append for its completed output prefix. This transparent
proof-side implementation may require quadratic total prefix-copy work in the
number of fields; it is not proposed as a production data structure or added
inference pass. Child execution costs remain the actual child's costs.

## Main checked statements

| Declaration under `YulangClosure.RecordBoundaryExecution` | Inputs | Derived conclusion |
| --- | --- | --- |
| `compiled_safe` | Actual successful compilation, independent input typing and presence evidence, `ChildrenSafe` | The complete record driver satisfies `SafeAll`, with `OutputsGood` on normal return. |
| `compiled_trace_invariant` | The same premises and an actual finite trace | The pending-plan/output/child invariant holds at its final state. |
| `reachable_required_present` | Such a trace ending before a required field | That field is actually present in the unchanged visible input. |
| `compiled_prefix_return` | Such a trace and actual returned observation | Target `ViewTyped` and exact visible-label intersection. |
| `compiled_prefix_request` | Such a trace and actual requested observation | Original packet admissibility and safety after every independently typed response. |
| `compiled_repeated_response` | One actual requested observation and two typed answers | Both applications of that same saved continuation satisfy the contract. |
| `native_filled_safe` | Actual indexed native-shape success and filling by one boundary-scoped resolver, input typing and child contracts | The filled plan satisfies the same full finite-prefix contract. |
| `child_request_exact`, `child_failure_exact` | Actual child observation equation | Exact packet/continuation-frame or failure-tag propagation. |

`native_filled_safe` applies `NativeRecordPlan.filled_compile` directly. It does
not infer a `RecMap_j` source node from an indexed solver query, or equate a
record-formal domain construction with an executable record adapter.

The concrete `Witness` payload machine can request a natural-number response,
return it, or loop internally forever. Its child contract is proved. A two-field
plan retains one required present field and one optional absence; the request
retains its original payload and pending field. The very same saved frame accepts
two different responses and produces the two corresponding typed outputs. The
spinning state meets every finite-prefix contract, making the absence of a
termination premise explicit.

## Validation and parent application

The pinned Lean 4.35.0 build and named-root audit passed at check03, with no
warnings in the new module. The four first audited roots use only `propext` and
`Quot.sound`. Checks01–02 failed on elaboration/implicit-argument mistakes; their
source snapshots and complete logs are preserved in the owned scratch directory.
No mathematical assumption, constructor or theorem conclusion was weakened to
repair those errors. A complete originating-module type/axiom census and fresh
nonauthor review are recorded in the associated review receipt and primary
progress record before integration.

The record-specific finite-prefix and resumption *composition* is now supplied
at this explicit abstract payload interface. Full original inference soundness
still requires source boundary construction with distinct input/output view ports,
actual child-contract production, contextual provider/world/guard correspondence,
all native histories and complete Call/source witnesses. The source domain,
optional-payload comparisons, failure classification and original native behavior
are unchanged.
