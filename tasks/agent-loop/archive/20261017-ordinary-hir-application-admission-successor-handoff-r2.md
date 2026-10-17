# Frozen handoff: ordinary-hir-application-admission-successor

Sprint: `choice-a-carrier-and-diagnostic-contract-repair-20261017`, revision 1.
Sprint SHA-256: `72622fda6e699ff6fdac22c362212e4a355eba0fe55690df5bd6e46f7de906b5`.
Assignment: `ordinary-hir-application-admission-successor`, handoff revision 2.
Successor artifact revision 2:
`notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`,
SHA-256 `9773bfe7631ccf2325435177c0a438cc637ca404bfb3b5863b7a827018d14c24`.
Revision 1 is preserved byte-for-byte at
`tasks/agent-loop/archive/20261017-ordinary-hir-application-admission-successor-r1.md`;
its handoff is preserved at
`tasks/agent-loop/archive/20261017-ordinary-hir-application-admission-successor-handoff-r1.md`.

Parent: original Yulang inference/execution goal; original A/B claims,
quantifiers and source/native obligations remain unchanged. Original theorem
conditions closed: 0. HIR-APP-CST-1 remains candidate pending combined compiler
review. HIR-APP-ADMISSION-1 remains OPEN pending three reviews and explicit
final user approval.

Baseline: `1a14f115ec3811f8f8133a09027ce9b5d6ad359d`. Frozen source audit:
`notes/theory/2026-10-17-choice-a-call-cst-source-key-audit.md`, SHA-256
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.
Direct source pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
notes/design/2026-10-10-ordinary-hir-successor-carrier.md c5fb75bdeb302a1f490398589b823f26d296d4cff3889cd0fddd5be4f801dad1
```

The predecessor spec review found two MAJOR conflicts: proposal rev1 wrongly
said ordinary HIR omitted its LocalSource carrier, and incorrectly promised
stable later numeric Error/Diagnostic IDs despite dense vector-index allocation.
Revision 2 preserves all existing ordinary SourceCarrierOutcome results,
forms and carrier occurrence ordinals; new canonical HIR child occurrences
append after that pass and map exact same parse keys with distinct IDs. The
error contract preserves per-module dense IDs, full retained payloads and
relative order, and explicitly states later numeric indices may shift when
application errors are removed or operand diagnostics are inserted. It adds no
sparse IDs or tombstones. Both consequences are named for final user approval.

Outcome class: repaired successor proposal, still not adopted. Code/test authority
remains zero. The original source constructor derivation remains conditional and
is not runtime evidence. No generated Call constraint, solver result, source T,
soundness, principality, termination or production claim follows.

Role/author: Luna primary `/root`, current session, requested/effective model
UNKNOWN. Exact author leases: successor design and this handoff; predecessor
copies are frozen under `tasks/agent-loop/archive/`. Writer STOPPED after freeze.
Reserved 240s conservatively charged because exact author duration was not
instrumented. No child workers wrote these files.

Checks: `git diff --check` and `python3 tools/agent_sprint.py check` passed.
No tests, builds, Cargo, compiler/runtime probes or source execution were run.
The three inherited UNKNOWN worker leases remain quarantined. Next: sequential
fresh spec, compiler (including source audit), architect review of these exact
bytes and direct pins. Any final approval remains separate from direction A.
