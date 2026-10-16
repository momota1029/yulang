# Frozen handoff: narrow Catch source/export spine repair

Sprint: `source-matched-catch-action-and-export-20261017`, contract rev4,
SHA-256 `abf5590a9c951ab3ec079a1c6cdf80180cefc00a4de80bcb3851f34a38d6b5d4`.
Assignment: `assignment-catch-source-export-repair-20261017`.
Outcome class: implementation repair; source/HIR/candidate observations remain
provisional and unknown until Luna's separately authorized single Cargo attempt.

Worker: `/root/catch_source_export_repair`; current runtime session/receipt
unavailable in exposed tools. Requested model/effort: `gpt-6-luna` / `high`.
Observed model/effort: UNKNOWN / UNKNOWN. Active-work acknowledgement with this
identity and model uncertainty was sent to `/root` before any write. No
descendants or coauthors.

## Exact repair and correspondence

The specimen remains byte-identical to the pinned 138-byte literal
(`9a86d2e0d0004cbdbd4be96dcdc284b6648287a203518c93211c43705f8ed8d3`). Its
Catch scrutinee is the full `(signal::ping())(1)` expression. The example now
checks the authentic callee spine by following owned LocalSource indices:

```text
outer Apply -> its callee Group -> Group inner Apply -> inner callee Operation
```

The terminal operation must resolve to the same declared `ping` Arc. Its
actual occurrence/key is still checked by `report_occurrence`. The outer Apply,
Group, and inner Apply now also have their actual occurrence/key ownership
reported. This authenticates the source forms and leaf occurrence without a
global operation search.

All previous declaration, binder/use, root/key, Apply inventory, ordinary
`CandidateInference::solve`, HIR observation, zero-conflict export gate,
`source_call`, `fresh_use`, and authentic-root export logic remains intact. The
original implementation handoff remains frozen and unchanged. The proof's
`CATCH-SPECIMEN-TYPED-INCIDENCE` premise remains open; no source typing,
handler adequacy, detached export, runtime execution, parent closure, or
production authority follows from this repair.

The native evidence chain remains source LocalSource construction in
`crates/yu-hir/src/module/local_source.rs` -> candidate source/constraint path
in `crates/yu-solver/src/candidate_source.rs` and ordinary solve/source-call
owner `crates/yu-solver/src/candidate_call.rs` -> the still-unrun example
observations. This change only fixes source authentication before those gates;
it adds no constraint, propagation, or execution claim.

## Frozen outputs and checks

1. `crates/yu-solver/examples/research_catch_source_export.rs` — repaired
   example, SHA-256
   `5095762ef3b92146e33a916b0663f6379b10024d06499099cec79afe0f6c80de`.
2. `tasks/agent-loop/inbox/20261017-catch-source-export-repair.md` — this
   handoff; its byte hash is sent separately to avoid a self-hash cycle.

Exact pre-repair snapshot retained unchanged at
`tasks/agent-loop/snapshots/20261017-catch-source-export-pre-repair.rs`,
SHA-256 `1a0d2aa3494ea2bb47e67a17f2bf3efb2ce895e3725f195f86a6018306cd0c94`.
The original implementation handoff remains unchanged at
`tasks/agent-loop/inbox/20261017-catch-source-export.md`, SHA-256
`7d24ae7115f2c418af6fb862e40b3e082d4344ab872b13f30605fbbe85f17c05`.

Static evidence: checked the exact contract/snapshot/handoff hashes; the
repaired example matched the snapshot before editing; reviewed a two-file
delta against that snapshot and confirmed only the expected spine-authentication
block changed. Frozen direct owner hashes matched the contract for
`local_source.rs`, `candidate_source.rs`, `candidate_call.rs`, the Catch test,
and both proof artifacts. No tests, build, Cargo, Git operation, extra path,
scratch output, generated output, or dependency edits were made. These static
checks do not validate compilation or runtime behavior.

The repair cap is 120 seconds from reserve; exact active-time instrumentation
is unavailable, so charge the full 120 seconds conservatively. No Cargo attempt
was used. Worker state: STOPPED after freezing both leased outputs; no
descendants or remaining writes.

Next step: fresh independent `regression_auditor` review of the complete
example and exact snapshot delta. Luna runs nothing until that reviewer accepts
the frozen target. Any later Cargo result remains provisional and must pass the
separate post-execution review.
