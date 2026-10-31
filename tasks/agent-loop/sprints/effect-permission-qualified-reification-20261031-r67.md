# Sprint EFFECT-PERMISSION-QUALIFIED-REIFICATION/20261031-R67 — reify borrowed source facts for qualified readers

Status: ADMITTED_BOUNDED_RESEARCH. Primary: Luna (`/root`). Branch `yulang3`; baseline `5ca4363b55ae2637b6858406fd85cce96bca28cc` (= verified `origin/yulang3`). Revision 1.

## Goal and exact outcome

Continue the unchanged Simple-sub/effect-hygiene parent. R66 proved the occurrence-qualified R65 reader through the R62 first-entry policy and the same R49 consumer Context, but Lean still accepts finite inventory rows independently of the actual borrowed Rust `InventoryPackage`. This sprint constructs a private, owner-scoped reifier of the package's fact/provenance rows and proves that occurrence-qualified selection commutes with the reification for R66's slot-0 Internal and slot-2 Lambda reads.

The Rust reifier must preserve the complete ordered semantic-fact table and every provenance edge, including repeated FactIds, exact occurrence equality, slot, fact index/identity, source-call/schema coordinates, and term/raw/canonical endpoint distinctions needed by `FactRow`. It must reject dangling or competing fact resolutions, same-key duplicate edges, foreign owner/package reuse, overflow and allocation failure; unavailable output cannot be represented as an empty inventory. Cross-owner validation happens before comparing owner-local ordinals. Use exact equality from the owning Rust types; do not replace artifact/store brands with unchecked integer casts or hashes.

The Lean module must model the same finite reification algorithm, prove finite occurrence-index reflection/injectivity, complete ordered edge and fact preservation, owner-scoped rejection, lookup commutation, selected-fact agreement (including all endpoint fields), and instantiate the agreement for the exact R66 Internal and Lambda reads. Preserve R66's R49 consumer application only under its existing premises. Do not assume `FaithfulExtraction`, a global FactId uniqueness property, omitted-row absence, or an independently mirrored package. If a term/endpoint or owner coordinate cannot be mapped from existing source data, stop at that exact missing owner premise and retain the successful partial proof honestly.

This is a finite reification/source-to-record step; it does not prove an actual native Run, complete R49 Context extraction, pointer/token identity correspondence in Lean, or the original A/B parent.

## Source and semantic limits

No changes to source language, generation, inference, routing, propagation, subtraction, runtime execution, expected output, or production authority. Keep all original A/B quantifiers, source domain, joint witness, scopes, occurrence multiplicity and local permission meaning. Reuse existing effect-hygiene proofs under their actual premises. Do not adopt the stale 2026-10-19 direct-Lambda R67 contract; that is a separate pending task.

## Frozen baseline and dependencies

- `crates/yu-solver/src/candidate_receiver.rs` — `253c0e469b91a30580a65ec57569a20ed7ad53fd7d7e82c0dc7d2e71102fad1a`.
- `crates/yu-solver/src/lib.rs` — `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `crates/yu-solver/src/candidate_context.rs` — `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- `crates/yu-hir/src/module.rs` — `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `crates/yu-solver/src/term.rs` — `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- R65 `OccurrenceQualifiedFactReadersR65.lean` — `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- R66 `OccurrenceQualifiedConsumerR66.lean` — `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`.
- R66 Rust handoff — `540f0ed4d616824f53860aa5b460a26953c129f0d409324e14361c39af0db787`.
- R66 proof handoff — `2d8c38878553713b475e32c6846be8a1c05a6b63d3345db1a851eb6660112039`.
- R66 independent review — `ac56e01d6ec413a96d12fc0f3b4664f8a926d0c55196886dd884aa7569c4534b`.
- R66 outcome — `24e41d60e902cad84ff4c56fb1edeb34c6975199d910a8af1596efd72c7f8c5e`.
- Top-level inference principles — `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Effect-hygiene integration — `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

Rehash exact inputs before writing and at freeze/review. R65/R66 modules and the named source files are read-only dependencies.

## Lanes and exact leases

**Rust — `/root/r67_rust`, implementer Luna/high, 1,400 seconds.** Write only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-qualified-reification-r67-rust.md`. Add a private borrowed owner-scoped reifier and connect it to `InventoryInternalRootView`. Preserve all input rows and original order. Use checked finite indices and exact source equality; every failure returns the existing private gap/error channel. No semantic or public API change.

**Lean — `/root/r67_proof`, lean_prover Sol/high, 2,200 seconds.** Write only `notes/theory/lean/YulangClosure/BorrowedQualifiedReadReificationR67.lean` and `tasks/agent-loop/inbox/effect-permission-qualified-reification-r67-proof.md`. Prove enumeration reflection, no omitted competitor, owner-scope separation, read commutation and application to R66's two source reads. Use pinned Lean 4.35.0 stdin-only checking and retain every theorem type and complete transitive axiom report.

**Review — `/root/r67_review`, fresh compiler_referee Sol/low, 1,200 seconds.** Launch only after both authors stop. Read-only; Luna persists the review at `tasks/agent-loop/inbox/effect-permission-qualified-reification-r67-review.md`.

**Luna primary: 1,200 seconds including 500 closeout.** Total cap 6,000 seconds; Astra 0. Existing checkout only. No worktree, environment, target, cache, scratch, build directory, Cargo, Rust build/test, Lake or generated output. `git diff --check` and the Lean stdin proof check are allowed. No tests are authorized.

## Review attacks and stopping conditions

Review two occurrences sharing one FactId, same-key duplicate edges, omitted/extra competitors, permuted semantic-fact rows, equal local ordinals from distinct HIR artifacts, foreign stores/packages, dangling fact indexes, and changed raw/canonical endpoints. Check source-code correspondence of the Rust enumeration against the Lean definitions before accepting the commuting theorem. Freeze all inputs/artifacts before review. Return an exact missing source owner if any reification property depends on an unrecorded pointer/token or endpoint conversion.

## Parent application and OPEN claims

A bounded PASS establishes only that this private finite reifier preserves the selected qualified reads under the admitted record correspondence. Actual Rust-to-Lean interpretation, native pointer/token/index authenticity, full provenance/provider/path completeness outside these tables, resource/failure correspondence, actual successful outer Runs, original A/B, whole-language effect hygiene, soundness, principality, termination and production remain OPEN. No semantic approval or production promotion follows.
