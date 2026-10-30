# R35 sprint — source-owned callback annotation row

Status: CANDIDATE pending manifest, current-state admission and exact lease dispatch.  
Branch/head: `yulang3` / `90fd99073` (R34 source-owner checkpoint). Existing checkout only.  
Authority: user's continuing Rust/Lean effect-hygiene and soundness objective; `AGENTS.md`; `rules/goal-driven-sprints.md`; R34 outcome and selector recommendation.

## Bounded outcome

Connect an actual `LocalSourceForm::Lambda` and its exact `LocalSourceParameter` to that formal's original `SourceAnnotation`, then retain a source-origin witness for the complete callback-result effect row. The row may be nested inside the annotation type (for example, under `Function.result`), so identify it by an exact structural path and polarity; direct top-level effects are insufficient. Bind the witness to the retained R34 HIR snapshot token, source root, lambda occurrence/range, formal identity, annotation owner/position, structural type path/polarity, row position, complete ordered concrete member list, and every symbolic row variable. Unsupported paths must be withheld explicitly, never treated as an absent or empty row.

The candidate witness must be issued only while lowering that exact Lambda/formal. A same-family row from another formal, source root, lambda, or annotation position must not satisfy it. Preserve duplicate members, order, and symbolic variables. If downstream R32 cannot represent a symbolic row, withhold downstream acceptance for that witness; never filter or drop symbolic entries. Keep R34 owner binding intact.

This proves source-origin and row-preservation facts for an annotation witness. It does not authenticate a row as a runtime Grant, emit requests, establish callback execution, or close the parent A/B obligations.

## Success and falsification gates

Rust/source: inspect the exact HIR→`LocalSourceParameter`→`Instruction::Lambda` path in the pinned non-quarantined sources. Add a storage-light witness at the real Lambda owner. It carries all listed identities and the complete row payload without structural/debug/name reconstruction. Every constructor and lowering route must either issue the witness from that exact formal or withhold it. No new environment, dependency, counter, cache, global state, or unbounded copy.

Lean: define a constructive source/Lambda/formal/annotation/row witness; prove exact owner, formal and position binding, rejection of foreign formals even when family identities match, complete ordered/multiplicity-preserving concrete row extraction, and exact preservation of symbolic variables. Apply the concrete-row case to R34/R33/R32 only when its representability premise is proved; symbolic rows must not manufacture a concrete success. Report exact theorem types and complete axioms at pinned Lean 4.35.0.

Independent review: audit source constructor coverage, every witness field and row member, adversarial same-family/other-formal and owner/position substitutions, proof construction, and all claimed downstream applications.

Falsifiers: another formal's same-family row is accepted; owner/occurrence/formal/position mismatch passes; a duplicate or ordered row member disappears or changes; a symbolic variable is erased; arbitrary row data is assumed authentic; or R32 acceptance follows despite an unrepresented symbolic member.

## Scope boundaries

Only use the existing checkout. `tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain quarantined under `UNKNOWN_WRITER`, excluded from reads and writes. No build, test, Cargo/Lake, environment/worktree/copy, target/cache, extraction, or scratch. Lean audits use pinned stdin under read-only bwrap. Rust is an uncompiled provisional source change; no execution or production claim.

The gate does not establish source-to-Grant/request wiring, selected-arm provenance, observations authentication, invocation lifetime, native `Step`/`History`, original A/B, full-language hygiene/soundness/principality/progress/termination, or production.

## Exact leases and resources

- Rust `/root/effect_permission_r31_rust`: `tools/inference-playground/src/runtime/program.rs`; `tasks/agent-loop/inbox/effect-permission-source-row-r35-rust.md`.
- Lean `/root/r35_proof`: `notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean`; `tasks/agent-loop/inbox/effect-permission-source-row-r35-proof.md`.
- Independent review `/root/effect_permission_r31_review`: read-only final handoff; Luna records the review in `tasks/agent-loop/inbox/effect-permission-source-row-r35-review.md`.
- Luna: this contract, exact input manifest/admission, stage ledger, current state and outcome `tasks/agent-loop/history/effect-permission-source-row-20261031-r35-outcome.md`.

Sequential dependency: freeze R34 and source inputs before writers start. Rust and Lean may work in parallel on disjoint leases. Reviewer starts only after both producers freeze. Fresh envelope 6,000 seconds: Rust 1,600; Lean 1,600; review 1,200; Luna 1,600 including 500 closeout; Astra 0. No R34 balance transfer. Record actual or UNKNOWN elapsed and runtime facts.

At closeout freeze a unique outcome, synchronize current state, run `python3 tools/agent_sprint.py check`, and stage only the exact reviewed checkpoint paths. Commit and push a safe fast-forward range without broad staging or force-push. A checkpoint must not include unrelated workspace changes or quarantined paths.
