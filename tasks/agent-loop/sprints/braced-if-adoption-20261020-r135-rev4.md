# Sprint: braced `if` compatibility proposal — R135 rev4

Status: **FROZEN CORRECTION CANDIDATE; rev3 is NOT CLEAN; no compiler implementation authority**  
Branch/baseline: `research/simple-sub-intrusion` / `94bd0aee28508a3316635e6f286a13f153598405`  
Parent goal and fixed outcome: unchanged from rev3. Prepare a reviewed user-decision-ready proposal for braced `if` bodies; do not implement or claim countdown support. Current colon-only authority, R132 failure, R64/R65 and all parent gates remain unchanged and OPEN.

## Revision reason and preserved evidence

R135 rev3 SHA-256: `9bcb21ebaefdc6feef5315efbfbd90ae5075b278253f21525438130c6fb1b696`. Its independent spec review found no major issue and one MINOR: add a Draft/unapproved design locator to `notes/design/INDEX.md`. Its independent compiler/source review found a MAJOR: the proposal misidentified Yulang2 brace-body lowering. Preserve both receipts and the reviewed bytes; rev3 is **NOT CLEAN** and must not be promoted.

The major finding is supported by frozen oracle owners:

- `crates/infer/src/lowering/expr/chain.rs` `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` — record guard precedes block lowering.
- `crates/infer/src/lowering/expr_syntax.rs` `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` — empty and compatible spread-only shapes can satisfy record recognition.
- `crates/infer/src/lowering/record_lit.rs` `88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c` — empty record and record-spread construction/effect path.
- Existing pins for Y2 `control.rs`, `group.rs`, and syntax design remain. Y3 solver owner `crates/yu-solver/src/candidate_source.rs` was inspected by the reviewer; that is implementation evidence, not a soundness proof.

The reviewer also found a MINOR in the proof note: current Y3 bare `else {` reaches the inline-boundary helper, emits Missing, and returns the brace without consuming it as an accepted body. Record this as a correction addendum; do not mutate the worker's frozen proof artifact.

## Fixed correction outcome

Produce an audited grammar-to-consumer mapping that separates: empty record; field/record-shaped groups; record-spread groups; non-record singleton expression groups; non-record multi-item groups; and mixed non-record spread groups. Analyze separator-only, malformed and ambiguous shapes from the pinned recognition predicate. State explicitly where historical Y2 implementation behavior is evidence and where a Y3 difference requires user approval. Do not select empty-as-unit, blanket spread rejection, or uniform expression-list semantics by implementation convenience.

Retain the countdown singleton argument only conditionally: the exact countdown bodies `{ 8 }` and `{ countdown true }` must be shown to take the non-record singleton route before its existing conditional consumer can be reused. No actual parser/HIR constructor, recovery, inference proof, source/native correspondence, countdown run or output `8` is established here.

## Exact leases and lanes

Old rev3 producer outputs remain frozen review evidence; changed content requires new sequential revisions and fresh delta review. This revision grants Luna the existing design/handoff paths and `notes/design/INDEX.md` solely for the exact corrections below. No other writer or Git lease is implied.

- **Proof correction lane, existing worker `/root/r135_braced_if_proof` after this revision is recorded:** new exact paths `notes/theory/2026-10-20-braced-if-elaboration-audit.md` and `tasks/agent-loop/inbox/20261020-r135-proof-audit.md`; max 120 seconds; source-attributed shape audit only, no claim to close the conditional proof, no source outside listed pins, no tests/builds/Git. Include Y3 bare-else Missing behavior and preserve P1–P4/open premises.
- **Luna design lane:** revise `notes/design/2026-10-20-braced-if-compatibility.md` and `tasks/agent-loop/inbox/20261020-r135-implementation.md`; max 60 seconds; add the non-authoritative Draft locator to `notes/design/INDEX.md`. Distinguish audited Y2 routes from unresolved Y3 choices; no implementation.
- **Fresh independent review:** compiler/source and spec reviewers inspect the frozen correction package; 180 seconds combined. The previous reviewers do not certify their own findings; use fresh eligible identities.
- **Closeout/integration:** 120 seconds shared with the existing closeout allocation. Only Luna stages exact paths and may commit/push a NOT-CLEAN record or later a reviewed proposal, never a semantic adoption.

## Dependencies, resources and stop rules

This sequential amendment adds the three oracle pins above and the exact correction paths. All unchanged authority, Y3, fixture, branch and runtime pins remain as in rev3 and must still match before any proof lease resumes. Rev3 used its full 1,200-second reservation. Rev4 adds **480 seconds** (120 proof audit, 60 design correction, 180 fresh reviews, 120 closeout/integration), for 1,680 seconds total; zero Astra. No elapsed UNKNOWN time is reclaimed. If the primary cannot establish budget/runtime availability, stop before resuming the proof writer and preserve its old frozen output.

No tests, builds, compiler/CLI, formatter, browser, source edits or generated artifacts. Stop if a required pin changes, a source shape takes a branch contrary to the audit, review has any open major/blocking finding, or a Y3 meaning would need to be chosen. User approval is still required before adopting any grammar/semantic difference and before a successor implementation sprint.
