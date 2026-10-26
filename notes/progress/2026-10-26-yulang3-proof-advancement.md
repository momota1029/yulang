# Yulang3 proof advancement — 2026-10-26

## Authority, baseline and ownership

The user's current request authorizes advancing the proofs and pushing the
result on `yulang3`. This work uses an isolated checkout initially at
`adfed0dbcc8875ac0c9e66c40a0b967b3e9df073`. It does not adopt a new language
decision, change the compiler, or revise the original Simple-sub A/B claims.

The existing R63 work and the unknown reservations recorded in
`tasks/agent-loop/current.json` remain owned by their recorded sessions. This
session does not reclaim those leases or rewrite their live scheduling state.
All proof outputs below are new, disjoint modules. The primary alone owns Git,
this progress record, integration audits and navigation updates.

The actual collaboration workers are `/root/execution_frontier`,
`/root/inference_frontier` and `/root/paper_allocation_execution`. They use the
generic-worker fallback with the checked-in `lean_prover` instructions; no
configured custom role or effective model identity is inferred from a role
name. Each is a leaf with no Git or compiler-write authority.

## Proof packets

| Output | Original obligation and intended contribution | Boundary retained |
| --- | --- | --- |
| `PaperTermSubstitutionAlgebra.lean` | Prove identity, composition and type/term commutation for the existing capture-avoiding operations; derive graph-formal and saved-response substitution equations and typed public API composition. | Omitted constructors retain the existing opaque fallback; the supported source language is not enlarged by an algebraic equation. |
| `PaperCallEntryFormation.lean` | Operational manuscript call-entry clauses: construct and type the actual code for both lambda modes and a complete finite wrapper spine, retaining the same owner and metadata. | Normalization to that spine, actual receipt/world formation and the full source-to-runtime bridge remain separate. |
| `NativeIntegerArithmetic.lean` | Native `decimal_add` and IntAdd/IntSub: prove the positional arithmetic meaning of the concrete digit loops and signed branches. | Successful primitive arithmetic does not establish whole native value/graph readback or inference soundness. |
| `PaperAllocationExecution.lean` | Compose actual fresh heap allocation with the paper executor and reusable saved responses; derive preservation from initial/source typing and actual operations. | Full source-rec elaboration, guarded observation/progress and nonempty-owner resumption are not supplied by a heap-payload theorem. |

Each proof packet has a separate handoff under `tasks/agent-loop/inbox/`.
Checker outputs are kept in task-local isolated projects until integration;
workers never share a writable Lake cache. The pinned native toolchain is Lean
4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with no additional
packages. The initial ordinary-sandbox attempt could not resolve the toolchain
application path; the authorized native invocation outside that restriction
reported the expected version. That execution failure is not a proof failure.

## Verification and review contract

Each module must pass actual Lean checking and a complete axiom audit, including
private/generated theorem declarations. The allowed standard axioms are
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, project axiom or
unchecked native-evaluation assumption is acceptable. Printed theorem types,
source correspondence and unresolved hypotheses are reviewed separately from
kernel acceptance. A fresh non-author review is required before a theorem is
described as accepted.

Focused isolated checks use one Lean process per worker, `-j1 -M1024`, with
finite timeouts. Integration runs the intended default target once and the
new explicit module audit. Record-only changes do not trigger broad repeats.

## Integration outcome

All four proof packets passed kernel checking and fresh non-author review for
their stated scopes. No blocking, major or minor finding remains. The primary
authored the term algebra; the other three packets were authored by the leaf
workers named above. Cross-review did not edit the reviewed sources or rerun
checks without a concrete need. This is an accepted component checkpoint;
the original whole-language and inference gates remain OPEN.

### Before and after

1. **Substitution.** Existing typed replacement did not give the raw algebra
   needed to identify two successive substitutions with one simultaneous
   substitution. The new proofs derive renaming/replacement identity and
   composition, type-substitution commutation, correct lift/shift laws under
   binders, literal graph-formal preservation, and the exact response vector
   `0 ↦ response`, `k + 1 ↦ rho k`. The checked `Option` API composition derives
   the second support check from typing. No replacement-composition law is
   assumed as an input.
2. **Call entry.** Existing Call typing did not construct the actual entry
   code. Both lambda modes and arbitrary finite wrapper nesting now construct
   one typed body and the manuscript's same-owner scoped entry trace. The body
   is shared by all subsequent admissible finite interactions. The explicit
   `value_entry_view_frontier` theorem also locates the missing executor case:
   a typed Value-lambda entry pushes its let frame and reaches
   `Force (View receipt thunk)`, for which the current partial executor returns
   `none`. This is a limitation of that partial executor, not a refutation of
   the original language's progress claim.
3. **Allocation and saved responses.** Fresh allocation and fixed-heap
   execution were separate. `History` now composes actual allocation, control
   steps, observation and exposed-request responses. State, heap-payload and
   saved-body typing are derived from initial typing and independent source
   block/substitution/freshness premises. The actual allocation body no longer
   needs extended-graph typing as an input. Replaying one saved packet through
   its real response interface supports later allocation and current-graph
   responses; the concrete node-10/node-20 example proves that the latter
   response could not have been typed in the save-time empty graph. The
   represented response case has empty owners, and replay is a new invocation,
   not an invented scheduler edge from an arbitrary final state.
4. **Native integer arithmetic.** The faithful carry/borrow and signed-branch
   model now proves arbitrary-width addition and subtraction, including
   leading zeros, negative zero and unequal digit lengths. It proves exact
   byte-to-String decoding and the native trimming/negation behavior. The two
   completed-request corollaries remove the old output `WellFormed` producer
   premise for these operations and fix the response literal to `a + b` or
   `a - b`, preserving the existing prefix, current-world, actual operation
   instance, metadata, suffix and continuation conclusions. This is a
   source-reviewed model of successful Rust helper bodies, not a formal Rust
   interpreter or a guarantee of allocation success.

### Default integration and complete audit

`lakefile.toml` retains the existing `YulangClosure` default target and root
glob, and adds the explicit `YulangClosure.ProofAdvancement` glob. The latter
imports all four modules. Thus ordinary default builds check the new proofs
without editing the concurrently reserved `YulangClosure.lean` root.
No compiler, dependency, toolchain pin, expectation, semantic authority,
foreign scheduling record or existing theorem statement was changed.

From `notes/theory/lean`, the reproducible checks are:

```sh
lake --no-cache build
lake env lean -j1 -M1024 AuditProofAdvancement.lean
```

The integrated default build completed successfully with **58 jobs**.
`AuditProofAdvancement.lean` enumerates theorem constants by their exact
originating module, includes private/generated helpers, rejects module axioms,
requires all 20 named application roots, prints each full type and axiom list,
and rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound`.
It completed with **538** unique, matched theorem records:

| Module | Authored theorem declarations | Complete module theorem inventory |
| --- | ---: | ---: |
| `PaperTermSubstitutionAlgebra` | 58 | 306 |
| `PaperCallEntryFormation` | 10 | 23 |
| `PaperAllocationExecution` | 24 | 50 |
| `NativeIntegerArithmetic` | 62 | 159 |
| Total | 154 | 538 |

The larger inventory includes generated equation and proof helpers, not 538
independent user-facing results. Exact axiom-list totals are 420 with
`propext`/`Quot.sound`, 68 empty, 3 with only `Quot.sound`, 19 with only
`propext`, and 28 with all three allowed standard axioms. No `sorryAx`, project
axiom, unchecked native-evaluation axiom or unapproved dependency occurs.

The original integration subprocess result was truncated during conversation
compaction, although both final success markers and process completion were
observed. To retain an explicit exit receipt, only the small complete audit was
repeated against the unchanged sources: exit code **0**, **2.235 seconds**,
538 records, identical log bytes. The default build was not needlessly rerun.

| Evidence | SHA-256 |
| --- | --- |
| Default build log, 58 jobs | `11c37ca02e1f88b47eef5f5efe4da5165dc07c615417d47d06993ba1ea0f0056` |
| Complete final audit log | `0d92bfba29b20072e627c1a71ad6ddc1e62f7fc2aca621a5f70f68de53f06c98` |
| Term-only complete audit, 306 declarations | `87c14204604cc51c97c864ef012fbe89539ad73785b8d656498114606b9faa0d` |

The task-local logs are under `/workspace/scratch/f98087c7ac1a/`; committed
audit code and the frozen sources reproduce the checks without those paths.
Build output replayed **668 existing dependency warnings**: 23 in
`PaperExecutionSyntax`, 235 in `PaperExecutionBinderLaws`, 3 in
`ControlComposition`, 96 in `PaperTermSubstitution`, 4 in `PaperCoreStep`,
276 in `PaperTypeBetaExecution`, 22 in `PaperTupleSplitExecution`, 2 in
`PaperPerformLetExecution`, and 7 in `NativeIntegerComparison`. They are unused
binding/simp and deprecated simp-name warnings in unchanged foundations. No
warning originates in a new module or the new audit. The term algebra narrowly
suppresses the unused-simp-argument linter on uniform constructor induction
proofs; kernel checking and the axiom audit remain enabled.

### Frozen proofs and independent reviews

| Proof | Source SHA-256 | Non-author reviewer |
| --- | --- | --- |
| Term algebra | `b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d` | `/root/paper_allocation_execution` |
| Call entry | `2465c5620b0b66f6029ab294134d9860cd8bf810ac25c5f30763cb709c7da31e` | `/root/call_entry_review` |
| Allocation/execution | `d5cd9f4499ec0c6e67e73a9444634671e43b507368c418b1d9ecec7fd57f0aa4` | `/root/inference_frontier` |
| Native arithmetic | `5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1` | `/root/execution_frontier` |

Handoffs retain source correspondence, hypotheses, checker evidence and theorem
types. Reviews independently inspect the frozen sources and supplied evidence;
they do not misrepresent log inspection as an independent checker rerun:

- [Term algebra handoff](../../tasks/agent-loop/inbox/20261026-proof-advance-term-algebra.md)
  and [review](../../tasks/agent-loop/inbox/20261026-proof-advance-term-algebra-review.md).
- [Call entry handoff](../../tasks/agent-loop/inbox/20261026-proof-advance-call-entry.md)
  and [review](../../tasks/agent-loop/inbox/20261026-proof-advance-call-entry-review.md).
- [Allocation handoff](../../tasks/agent-loop/inbox/20261026-proof-advance-paper-allocation.md)
  and [review](../../tasks/agent-loop/inbox/20261026-proof-advance-paper-allocation-review.md).
- [Arithmetic handoff](../../tasks/agent-loop/inbox/20261026-proof-advance-native-arithmetic.md)
  and [review](../../tasks/agent-loop/inbox/20261026-proof-advance-native-arithmetic-review.md).
- [Default-build/audit integration review](../../tasks/agent-loop/inbox/20261026-proof-advance-integration-review.md).

### Remaining original obligations

The original whole-language theorem remains open with unchanged scope.
Concrete next seams are actual Force/View receipt and scope execution;
normalization from arbitrary callable values to the handled entry spine;
nonempty-owner/current-world/lifetime and release semantics; full source-rec
ordering, guarded heap formation and observation termination; remaining
source/native representation and primitive cases; and the original inference
soundness/completeness/principality A/B obligations. The new algebra does not
turn opaque raw cases into covered source cases. Finite preservation does not
prove progress, no-Bad, guardedness or termination. No parent gate or production
gate is promoted by this checkpoint.
