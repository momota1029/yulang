# R278 independent review receipt

Disposition **PASS_CONDITIONAL_ONLY**. Reviewer `/root/r276_production_entry_clean_review`, coordination session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`, requested/observed role-bound `compiler_referee`, `gpt-6.1-sol/medium`; independent runtime telemetry unavailable. Full **600-second reservation charged**, including contract and resume gates. Reviewer STOPPED; no writes, descendants, tests, builds, probes, Cargo, Lean, runtime, external paths, scratch/cache files or stage-2 reads.

## Source-first result

Before opening either frozen R278 output, the reviewer independently reconstructed R277-E001 `candidate_receiver.rs:2999–3013`:

- `assemble` filters `hir.items()` to `HirItem::Binding` entries.
- It returns `Err(unavailable())` unless the filtered binding count is exactly two, or if any `HirItem::Expression` occurs.
- Other item variants are ignored by this initial guard; the source does not require exactly two total HIR items.
- `unavailable()` at 2951–2952 is `CandidateError::Unsupported`.
- Under `H_count` (exactly one top-level Binding), count `1 != 2` is true and short-circuits before the expression scan, `answer` comparison at 3017, or carrier lookup. The public entry propagates the error at `3160` before collection at `3161`.

The reviewer independently authenticated all contract-listed pins, R277-E001 index/range metadata, whole-file hash, exact 9,723-byte source interval and payload digest. Only E001 was rendered as technical source; no test boundary appeared.

## Frozen-output adjudication

After recording source-first derivation, the reviewer inspected the frozen R278 theory and handoff. Both accurately state the conditional guard result and preserve the distinction among:

1. the source-derived `assemble` condition;
2. incompatibility if `H_count` holds; and
3. the still-unproved production source-to-HIR census.

The producer does not establish that the fixed source parses/lowers successfully, yields one top-level Binding, or supplies a same-HIR outer `DefinitionRootId R`. A parse/lowering exit remains distinct from `assemble` rejection. The normal-execution qualification for collection/allocation is accurate. The first guard requires two Binding entries, not two total `HirItem`s. No major, minor or blocking defect was found in the bounded conditional claim.

No actual witness rejection, accepted-source counterexample, ordinary-source rejection, global unreachability, production finding, R71 result or parent closure is established. Parent/A/B remains 0→0; `Need_D`/R71 OPEN; `NO_SAFE_CODE_SLICE`.

Frozen artifacts remain:

- Theory `notes/theory/2026-11-03-public-entry-guard-incompatibility-r278.md`, SHA-256 `bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e`.
- Handoff `tasks/agent-loop/inbox/public-entry-guard-incompatibility-r278.md`, SHA-256 `fe761f634a1c4d17a516f93112c764eb40f284ad09dfd768034e7ba38e58a27c`.

Next material boundary: primary consults the dispatcher on whether the reviewed conditional obstruction justifies a separate source-to-shape bridge stage. Stage 2 remains unissued pending that decision and a separate Luna view/GO.
