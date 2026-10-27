# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — reviewed outcome

## Disposition

**ENDED_REVIEWED_FINITE_ONLY.** The fixed outcome—one authentic same-owner
inline Lambda/Apply extraction instance and a finite Lean consumer—was reached
and accepted by fresh independent review with no blocking, major or minor
findings for this exact fixture. This is a real source-to-trace-to-Lean
checkpoint, not closure of the full Yulang inference/executor goal.

## Before/after evidence

Before the final run, Cargo call 5/6 failed before extractor execution with
three unavailable `PositionId::ordinal()` calls and seven error conversions
from `HirAvailabilityError`; no trace existed. That call and all raw receipt
hashes are preserved in
`tasks/agent-loop/history/20261027-r2-cargo-call5-failure.md`.

The frozen extractor repair maps each authenticated `PositionId` to its exact
position-table entry and preserves fatal HIR availability errors. Final Cargo
call 6/6 ran exactly once, offline and locked, under 1 CPU/1 GiB/120s; it exited
0 after 1.46 seconds. Stdout reports eight authenticated parse keys/HIR
occurrences, 22 source-position rows, raw Group callee → projected Lambda,
distinct nested same-spelling parameter identities, two ordered StatementBlock
entries and foreign-owner rejection. The generated trace is consumed by twelve
checked Lean theorems; each has a complete empty transitive axiom set. A fresh
compiler referee independently matched the source, trace, call receipts, proof
artifacts and 656-entry Lean source-cone manifest, and accepted this finite
fixture without findings.

## Frozen artifacts

- rev6 contract:
  `tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2-rev6.md`,
  SHA-256 `a650bdbd86b3b88fe18d7b1200e4303b7237e3db4863411d075b11891529fbde`.
- repaired extractor `tools/inline-authentic-extraction/src/main.rs`, SHA-256
  `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`.
- implementation handoff rev5, SHA-256
  `976fc2b754263b3afb534dfcc32e1e00895269036f0378fc3c732cce0de345b9`.
- generated trace, SHA-256
  `73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3`.
- Lean consumer, SHA-256
  `ed25ec65c5760e4a523fabe75f392c67476a710d3af60e345c07e5bf5eaeeb09`;
  audit SHA-256
  `85e0dd8adcef88c9e10c6aebde526dcb2340a1f58e03a67a5dd4e903f08ad089`.
- proof handoff, SHA-256
  `d0a8da28f7bca9d9055dd4840ef7dfdad9a91aae55378b13e4bd9e152c555612`.
- independent review:
  `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2-review.md`,
  SHA-256 `3913081d0cafd2b7f9fbccbb6b5bfc0cfc69f54c7057d64f7841544bb0f95927`.

## Exact scope and remaining obstruction

The accepted trace covers one unannotated outer Lambda with a StatementBlock,
one `MlArgument` Apply tail, one raw Group edge to a nested same-spelling
Lambda, the inner-body Name, outer-parameter argument and restored final Name.
The Apply range `(29,30)` is the argument tail; it does not contain the raw
callee range `(19,28)`. The finite consumer checks the actual convention. It
does not claim that emitted Bool flags or foreign-owner report strings prove
Rust execution behavior; those runtime assertions are supported by the frozen
Rust source and call receipt and reviewed as such.

The first parent-blocking missing premise remains the original-source/frontend
allocation equation. No inspected owner constructs the required original
`Identity` tuple—resolved declaration, ambient `ScopeEntry` list, Context,
Lambda/formal/admin-wild/Name Sites, Name, Apply Site and actual argument—from
the authenticated Rust/HIR/source identities. `OriginalIdentityEntryOrigin`
theorems assume that tuple and were not specialized. The finite result also
does not cover binding-statement initializers, Sequence cases or the full
supported source domain.

All original A/B, soundness, effect hygiene, principality, progress/termination,
complete Call, source/native, whole-language, receipt/admission and production
gates remain **OPEN**. No compiler semantics or production behavior changed.
R2 resource use is terminal at Cargo 6/6; Lean used three helper wrapper calls
and 8.359 seconds as reported in the checked handoff; Astra usage is 0. No
worker, Cargo/Rust process or Lean checker remains active. The full user goal
continues beyond this sprint.

The next sprint outcome is selected separately at the r2 END boundary; it must
target the original-source/frontend allocator bridge or a still higher-leverage
parent premise, without narrowing the original goal.
