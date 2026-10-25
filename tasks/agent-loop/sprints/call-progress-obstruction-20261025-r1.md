# LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r1

Status: **READY; not yet activated**. Baseline: `8fd63cadc` on
`research/simple-sub-intrusion`. Parent goal: complete Lean proofs of Yulang
semantics and type inference; the original Call progress/A-B and source/native
obligations remain OPEN.

## Outcome and exact claims

Construct a well-typed initial Call and an actual five-step `CallControlStep`
prefix reaching the existing View-wrapped Force head, then establish that this
head has no successor in the current formal relation. The result records a
formalization obstruction; it says nothing about source reachability or native
execution.

### P — `viewed_force_reachable`

Owner: constructive prover, Sol/high, 900 seconds. Exact outputs:

- `notes/theory/lean/YulangClosure/CallViewedForceReachability.lean`
- `tasks/agent-loop/inbox/20261025-call-viewed-force-reachability.md`

Construct `term : TypedCall.CallTerm` and `target : CallState W` for any world,
metadata, occurrence, literal suffix and independently typed suffix, with
`U := Original.Ty.base .unit`, such that:

```lean
FramesTyped sig suffix (.original U) result →
∃ term target,
  Prefix (CallControlStep md) 5
    (CallState.initial term world suffix) target ∧
  target.head = .active
    (.force (.view (.delay (.ret (.original .unit))) occurrence))
```

The term is a Value-entry identity lambda, identity result consumer, empty
wrap/interface plan, and the carrier `.view (.delay (.ret (.original .unit)))
occurrence`. Its actual five transitions are `start`, `attachReceipt`,
`enterLambda`, and two `enterBind` steps. Preserve all actual `CallTerm` fields:
function typing, thunk carrier typing, source receipt equality, wrap-plan
equality and receiver freshness. Do not claim source authenticity.

### Q — `viewed_force_no_successor`

Owner: separate constructive prover, Sol/high, 300 seconds. Exact outputs:

- `notes/theory/lean/YulangClosure/CallViewedForceStuck.lean`
- `tasks/agent-loop/inbox/20261025-call-viewed-force-stuck.md`

For arbitrary metadata, state, value and occurrence, prove:

```lean
s.head = .active (.force (.view value occurrence)) →
¬ ∃ t, CallControlStep md s t
```

Invert all current transition constructors. No typing, reachability, suffix,
frame or metadata-law premise may be added.

### Luna composition — `reachable_typed_viewed_force_stuck`

Using P, Q, and accepted `initial_call_prefix_terminal_typing`, prove that the
same five-step endpoint is `CallStateTyped sig target result`, retains the
exact View-wrapped Force head, and has no successor, given the independent
`FramesTyped sig suffix (.original U) result` premise. Keep returned/requested/
failed endpoint claims separate. Do not alter existing transition rules.

## Authority, inputs and limits

The formal definitions are pinned at the baseline. Relevant source SHA-256:

| Input | SHA-256 |
|---|---|
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CallPrefixTyping.lean` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `CallTerminalTyping.lean` | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| `CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| finite-typing accepted outcome | `call-finite-typing-20261025-r1-outcome.md` (accepted/CLEAN; hash recorded in verification receipt) |

The accepted finite-typing theorem only preserves supplied typing along an
actual finite prefix. It does not establish progress. Q is only a fact about
the present inductive relation. No Rust/source producer, frontend realization,
source/native correspondence, Call A/B, inference A/B, semantic approval or
production claim is in scope. The Force source producer/consumer path remains
unresolved, so the implementation lane is `NO_SAFE_CODE_SLICE` after inspection
of `CoreExecution.callEntryBody` and both Force constructors in
`ControlSyntax.lean`.

## Verification, review and stop rules

- Total fresh envelope: 2,700 seconds: P 900, Q 300, composition 240,
  serialized verification 480, fresh independent review 600, integration 180.
- Astra: 0. At most six active/reserved/unknown assignments including the three
  preserved UNKNOWN quarantines; P/Q are the only new authors. Reviewer starts
  after both authors STOP and their exact outputs are frozen.
- At most four serialized Lean invocations total: P, Q, composition, exact
  signature/axiom query. Each: `lake env lean -j1 -M1024`, timeout 120 seconds,
  one process, 1 CPU, 1 GiB. No tests or unrelated builds.
- Stop at the first pin mismatch, proposition mismatch, Lean failure or
  timeout. Do not repair within this frozen revision; a changed claim needs a
  new revision. No `sorry`, new axioms, or changed semantics.
- Luna alone owns `current.json`, review assignment/adjudication, explicit-path
  staging, commits and push. Preserve all unrelated untracked Force records.

Exact Luna outputs:

- `notes/theory/lean/YulangClosure/CallProgressObstruction.lean`
- `notes/theory/lean/.lake/call-progress-obstruction-r1-check.lean`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r1-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r1-review.md`
- `tasks/agent-loop/sprints/call-progress-obstruction-20261025-r1-outcome.md`
