# Q: View-wrapped Force has no successor

- Sprint: `LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r2`.
- Contract SHA-256: `01aa44596c1f2aeae77afb0c90f5026fc263e522b7771c2ced274deb957f9e9c`.
- Governing r1 SHA-256: `6020b57d97d0642be5702dafe52efa5fc302165ded16d5e717a159b7e92bee5c`.
- Assignment/handoff: `CALL-VIEWED-FORCE-STUCK-Q`, revision **1**.
- Author/worker: constructive Q author `/root/view_force_stuck_prover`; current tool-backed activation from Luna under r2. No descendants or coauthors.
- Requested model/effort: Sol/high. Observed model/effort: **UNKNOWN/UNKNOWN**; no runtime metadata receipt exposes either here.
- Activation baseline supplied by Luna: `9cdcab55e`; no Git command used. All nine r1 source pins and both contract hashes rechecked and matched.

## Candidate and parent application

Outcome: **candidate**, source frozen before compilation. The exact theorem is
`YulangClosure.Control.viewed_force_no_successor`, with arbitrary
`{W : Type} {md : Metadata W} {s : CallState W}` and arbitrary
`{value : TypedCall.Value} {occurrence : TypedCall.ViewOccurrence}`:

```lean
s.head = .active (.force (.view value occurrence)) →
¬ ∃ t, CallControlStep md s t
```

No typing, reachability, suffix, frame, or metadata-law premise is added. The
proof inverts an alleged transition and contradicts its source head in every
constructor. It uses no `sorry`, new axiom, or semantics change.

Luna can apply Q to P's exact five-step target using P's head equality, then
combine accepted finite-prefix preservation with P's independent suffix typing
premise. Q alone proves neither reachability nor typing. The original Call A/B,
source/native correspondence, inference A/B, and production gates remain OPEN.

## Exact source evidence and constructor coverage

`ControlSyntax.lean:164` owns `CallControlStep`. Its current 28 constructors are
all visited by `cases hstep`:

1. `start`: initial head is `.call`, using `CallState.initial` at line 138.
2. `peelWrap`, `attachReceipt`: source head is `.enter`.
3. `enterLambda`: source head is `.received`.
4. `enterBind`, `enterOriginal`, `enterScope`, `enterExpose`, `emitRequest`:
   source active computation is respectively `.bind`, `.original`, `.scope`,
   `.expose`, `.request`.
5. `originalStep`, `originalExit`: source head is `.originalState`.
6. `forceDelay` (line 299): source Force operand is `.delay`.
7. `forceEmbeddedOriginalDelay` (line 310): source Force operand is `.original`.
8. `returnBind`, `returnAdapter`, `returnScope`, `returnExpose`, `finishReturn`:
   source active computation is `.ret`.
9. `requestBind`, `requestAdapter`, `requestScope`, `requestExpose`,
   `finishRequest`: source head is `.requesting`.
10. `failBind`, `failAdapter`, `failScope`, `failExpose`, `finishFailure`:
    source active computation is `.fail`.

The two Force constructors reject `.view` by constructor disjointness. No
constructor has a View-wrapped Force source. This is evidence about the actual
frozen Lean constructors, not a test assuming hypothetical transitions. There
is no Rust/frontend/native evidence in Q. `TypedCall.callEntryBody` and the two
Force constructors are the formal construction/consumer seam; a source producer
bridge remains outside Q and owned by Luna's source-realization lane.

## Frozen artifacts and dependencies

New source: `notes/theory/lean/YulangClosure/CallViewedForceStuck.lean`.
SHA-256: `71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9`.

Direct import: `YulangClosure.ControlSyntax`.

| Dependency | SHA-256 |
|---|---|
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |

The accepted finite-typing theorem is reused only by Luna's planned composition;
Q imports no typing theorem and treats preservation as no progress evidence.
No historical conditional proof or failed construction is used.

## Checks, resources, next step, and stop receipt

- Static read of every current transition constructor and exact hash checks:
  completed; pins match. Omitted current transition constructors: none.
- Lean/test/build invocations: **0**. Lean validation and independent review:
  **NOT_RUN**. No generated output created. No scratch paths.
- Budget: 300 seconds active work granted; elapsed active work is not exposed
  by runtime metadata, so exact spent/remaining seconds are UNKNOWN. One Lean
  invocation remains reserved, requiring Luna's explicit compiler ticket.
- Authorized invocation, only after ticket: from `notes/theory/lean`,
  `lake env lean -j1 -M1024 YulangClosure/CallViewedForceStuck.lean`, 120-second
  maximum. Stop on the first failure, timeout, or pin mismatch; no repair in r2.
- Exact remaining Q premise: successful elaboration against the pinned relation.
  Owner: Q after Luna grants the ticket. Fresh independent review belongs to Luna.
- TODO `Q-COMPILE-1`: Luna grants serialized ticket after P stops; Q runs the
  single invocation against this frozen source. Falsifier: any elaboration
  failure, timeout, or pin mismatch.
- TODO `Q-COMPOSE-1`: Luna combines P, Q, and accepted finite typing, retaining
  independent suffix typing. Falsifier: failure to derive endpoint typing or
  preserve the exact target head under the original quantifiers.
- Writer state at freeze, `2026-10-25 03:52:26 UTC`: **WAITING**, writes stopped
  pending ticket and acknowledged revision update. No live compiler or descendant.
  Source revision is immutable. This handoff will require a new sequential
  revision for the later compilation receipt; it is not yet an approved theorem.

Exact lease additionally permits the `.olean` and `.ilean` counterparts under
`notes/theory/lean/.lake/build/lib/lean/YulangClosure/`; neither exists as an
output of this assignment yet. Only the source and this handoff have been written.
