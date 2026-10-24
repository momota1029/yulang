# LEAN-CORE-CONTROL-PROOF-20261024 / handoff revision 1

Sprint: LEAN-CORE-CONTROL-BRIDGE-20261024/r3.
Contract: `tasks/agent-loop/sprints/lean-core-control-bridge-20261024-r3.md`,
SHA-256 `4853f6713bd6b42b509c4f26085b90c2860156695af8c70f247fa35269400044`.
Baseline supplied by Luna: `fbbc66cdc63b1f227fff30d33355fc6c35f9dd59`.

## Outcome and parent application

**Outcome class: unchecked candidate proof code.** No Lean checker result or
independent review was received in this assignment. The unchanged parent is
the full Yulang semantics/type-inference, original source/native and A/B goal;
it remains OPEN. This packet must not be recorded as a reviewed theorem.

The candidate `CoreControlBridge.lean` directly represents Original values,
computations and syntax-bearing frames. It maps each actual Original step,
including entry, `substComp (single v)` return-bind and all six Principal
constructors, into the four frozen Control transitions. Arbitrary old Control
suffixes remain literally behind the explicit boundary.

`successor_coverage` classifies every internal Control successor of the
delimited image as an Original step or the explicit boundary exit.
`finite_transfer` and `finite_coverage` transfer all finite prefixes and split
arbitrary Control prefixes at that exit. `machine_finite_transfer` and
`machine_finite_coverage` do the same for the root machine: legal external
resumptions are impossible before exit by the actual `suspended` predicate,
and remain independently quantified in the ordinary post-exit foreign trace.
No single local action is claimed to prove foreign continuation behavior.

`embed_typed` derives **SegmentTyped**, as r3 requires, from the actual closed
Original state judgment and independently typed suffix. `exit_typed` derives
ordinary Control StateTyped only after boundary handoff. Candidate
`segment_preservation`, `finite_typed_transfer` and `finite_closed_safety`
apply the correspondence back to the existing Original preservation/progress
parent. The closed corollary covers every finite internal Control trace with
empty foreign suffix and states segment-or-ordinary typing, Bad exclusion,
and terminal return or a concrete successor. Ordinary suffix safety after
exit retains the existing body/typing premises.

The exact remaining first premise is **Lean elaboration/kernel acceptance of
these candidate declarations against the frozen r3 implementation**, owned by
Luna's checker/integration lane. In particular, dependent Prefix induction and
record/embedding definitional equalities have not been machine checked here.
Fresh independent proof review follows acceptance; this author is ineligible
to certify the combined result.

## Evidence and limits

Reused within actual premises: Original.Principal, Step, FramesTyped,
step_preservation, progress, and the established typed substitution carried by
the actual Step.returnBind constructor. Closed typing remains exactly
`emptyContext`; no open-context typing theorem is inferred.

Rejected: arbitrary Nat encodings, a same-syntax BodyLaws assumption, and
un-delimited all-successor coverage with an arbitrary foreign suffix (a
source return could activate a suffix bind). Luna's versioned r2 boundary and
r3 separate typing domain resolve that specific composition seam without
adding a source construct or an implicit exit.

Source/consumer evidence is the exact formal path:
`Original.Step.enter/returnBind/principal` -> actual syntax and substitution
-> `ControlStep.originalEnter/originalReturnBind/originalPrincipal` ->
`originalExit` -> ordinary suffix. No new compiler constructor/native execution
evidence was produced. The sprint's `begin_local` motivation is not promoted
to a native correspondence proof by this packet. Full Call/wrap/Resume, all
other raw constructors, source initialization, metadata/observations, native
realization, source-scoped coverage/principality/termination and original A/B
remain open at their existing owners.

## Frozen bytes and authors

Sole proof/handoff author: `/root/lean_core_control_prover`.
Implementation dependencies: `/root/lean_control_prefix_impl`; Luna supplied
the r2/r3 interface decisions. No descendants or independent reviewers ran
under this assignment.

| Path under `notes/theory/lean/YulangClosure/` | SHA-256 |
|---|---|
| `CoreControlBridge.lean` | `95cad83ee84e767aecd6314f84e983db40a9efba1e8322c6f54ee79d45c3cfad` |
| `ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `ControlTyping.lean` | `1c057f1f5303db479d0fc303bd1a0b305ba839f3034770dc467068c9f1869981` |
| `ControlComposition.lean` | `b2cce8eca5163dc41ef41c7cdeae5bc9dfb5186c67a982a7248194cef44b7437` |
| `CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |

Implementation bytes above were observed at 2026-10-24 14:11:24 UTC; Luna must
reconcile them with the implementation owner's frozen receipt before checking.

## Checks, resources and exact next handoff

Requested model/effort: Sol/high (`gpt-6.1-sol` requested by the parent).
Observed model/effort: **UNKNOWN/UNKNOWN**; no runtime metadata supplied it.
Actual worker identity: `/root/lean_core_control_prover`, current assignment
received through the supported collaboration runtime. Session label supplied
by sprint: `LEAN-CORE-CONTROL-BRIDGE-20261024/root-turn-1`.

Resource grant: 1,200 seconds, no descendants/Astra, builds/tests/compiler
changes/network/Git. First observed clock: 13:55:06 UTC; final freeze clock
observation: 14:11:24 UTC (978 seconds between observations). Exact launch
timestamp and active duration remain UNKNOWN; the assignment stops
conservatively rather than spending an unobserved remainder. No checker,
build, test or native probe ran in this leaf. Read-only source/declaration
inspection and byte hashing are the only evidence checks.

- TODO `LCCB-PROOF-CHECK-1`, Luna: check frozen r3 modules and this candidate
  with pinned Lean, then return exact diagnostics or acceptance/axiom receipt.
  Falsifier: any failed declaration, missing successor, changed substitution,
  suffix loss or hidden body-safety assumption. A green assumed-transition
  test is not substitute evidence.
- TODO `LCCB-PROOF-REVIEW-1`, Luna: appoint a fresh nonauthor reviewer only
  after coherent frozen acceptance; inspect exact theorem domains and the
  independent post-exit foreign trace quantifier.
- Implementation mutual TODO: reconcile the final Control dependency hashes
  above and r3's four authorized source transitions. This proof neither edits
  nor authorizes another lane's files.

Only new/written paths:
`notes/theory/lean/YulangClosure/CoreControlBridge.lean` and this exact inbox
file. No scratch or generated paths. No central records, production files,
tests, expectations, rules, semantics, questions or other workers' files were
written. **STOPPED: all proof and handoff writes cease after this revision is
hashed and submitted.** No unresolved descendants. Pending checker/review and
integration, not commit-ready theorem closure.
