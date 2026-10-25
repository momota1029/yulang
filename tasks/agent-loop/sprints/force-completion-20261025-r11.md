# Sprint FORCE-COMPLETION-20261025 — arbitrary-focus finite completion

Status: FROZEN ACTIVE CONTRACT
Branch / baseline commit: `research/simple-sub-intrusion` / `199c9eb15`
Authority: r7 accepted abstract definitions; current r10 boundary decision; `rules/goal-driven-sprints.md` §§1–7
Contract revision / primary approval: r11 / Luna primary

## Original outcome and success evidence

Original goal remains complete proofs for Yulang semantics and type inference in `notes/theory/lean`; original N1/O-NORM/O-RESULT/source-native/parent claims retain their original scope and remain OPEN. This packet addresses only a local mathematical completion lemma in the already accepted abstract r7 machine.

Prove in `notes/theory/lean/YulangClosure/ForceCompletion.lean`, importing the frozen `ForceAdmin.lean`, for all payload types `P`, fixed parameters `H`, `beta`, and `inst`, every initial focus `s`, exact event trace `tr`, output head `out`, and literal ordered wrappers `Ws`:

```lean
FocusResult H beta inst s tr out Ws ↔
  CountedRun H beta inst tr s ⟨headValue out, [], Ws⟩
```

Success requires a kernel-checked theorem with both directions, arbitrary fixed `inst`, exact trace equality, and literal wrapper order. No `sorry`, `admit`, custom axiom, extra hypothesis, or assumption of the target machine run inside `FocusResult` is allowed. A theorem failure or need for a new premise is an honest bounded obstruction.

This generalizes r7's accepted empty-stack equivalence to an arbitrary existing administrative focus. It is an abstract zipper-completion result only. It supplies reusable reasoning toward O-NORM but establishes no source encoding, concrete packet opening, Force/View applicability, O-RESULT, source/native correspondence, foreign-continuation theorem, Call theorem, or parent closure.

## Two continuing lanes

**Proof lane:** one `prover` constructs the forward direction by structural recursion on `StackResult` and `CountedRun.trans`, combines with `observe_run`, then constructs the converse through `run_backward` and `terminal_result`. It may add related private lemmas in the single leased module. It writes one handoff. Preserve exact pending-stack impossibility for node heads, saved outer wrappers, instantiated inner wrappers, and lifted event order. Stop on a required semantic premise or at 900 seconds.

**Implementation/source lane:** Luna carries forward r10's `NO_SAFE_CODE_SLICE`. The already inspected binder/export and Delay/normal-Force return owners still lack source-selected packet-opening and exhaustive result correspondence/allocation certificates. No compiler path is leased. This independent source seam remains OPEN and is not delayed by the abstract proof.

No Astra assignment: this is a bounded structural induction over a small frozen Lean model; no distinct core risk justifies Astra. No complementary author is useful until the exact proposition is checked. A fresh nonauthor proof reviewer will inspect frozen artifacts after author STOP.

## Frozen inputs and dependencies

- Baseline at author admission: `199c9eb15` (the reviewed r10 outcome/current synchronization commit).
- `notes/theory/lean/YulangClosure/ForceAdmin.lean`, SHA-256 `620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97`.
- r7 accepted outcome `tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r7-outcome.md`, SHA-256 `b89cbb133006aaae4563789460466ddc790df1460418f124dee36d86b5558d29`.
- r10 bounded outcome `tasks/agent-loop/sprints/force-declarative-construction-20261025-r10-outcome.md`, SHA-256 `5f445c4e693387496a3d9a232c9ed9f273509dd6c1f71aa6e6de8e890f80c62d`.
- r10 N `tasks/agent-loop/inbox/20261025-declarative-packet-construction.md`, SHA-256 `889b0c68c5508a70650dc4d6e43a39a71699454f9c92fad4af49b91c3664c652`.
- r10 R `tasks/agent-loop/inbox/20261025-force-return-entailment.md`, SHA-256 `414b6c301d66bf1d331c8b4d4944f230ec1e886b1f5d4fcc74e046d61b99c12f`.
- r10 fresh review found both bounded reports CLEAN only; their theorem promotions remain BLOCKING.

Revalidate these hashes before author launch and before final integration. Any changed proof dependency returns to Luna; no lease may overwrite an existing file.

## Exact leases, checks, resources

- Author `/root/force_completion_r11`: only new `notes/theory/lean/YulangClosure/ForceCompletion.lean` and `tasks/agent-loop/inbox/20261025-force-focus-completion.md`; requested Sol/high; observed settings must be recorded as returned or UNKNOWN.
- Reviewer: fresh eligible nonauthor, read-only on both frozen author artifacts and direct dependencies; 450 seconds.
- Luna: serialized Lean 4.35 check only after author STOP and frozen hash, command `timeout 120s env LEAN_NUM_THREADS=1 lake env lean YulangClosure/ForceCompletion.lean` from `notes/theory/lean`; capture exit, wall time, and `#print axioms` for the theorem. Do not run tests/builds.
- Luna integration/current/outcome/Git: 330 seconds.
- Fresh total cap: 1,800 seconds: author 900 + reviewer 450 + one Lean check 120 + Luna integration 330. No carryover. One Lean process, one CPU, 1 GiB, 120-second timeout. Astra zero. No tests/builds/compiler runtime/source edits.
- Three legacy UNKNOWN reservations remain quarantined. Admit only this author; reserve reviewer and integration slots. Reviewer starts only after author STOP; do not exceed sprint/global limits or reclaim unknown leases.

## Review and integration boundary

Freeze the module and handoff before review. Independent review must check both implication directions, induction coverage for every `StackResult` constructor and `AdminMicro` case used, exact wrappers/trace, parameter generality, direct imports, and axiom output; primary Lean check is separate evidence. Author cannot review. Any blocking proof/review finding is batched before repair under a new artifact revision and within remaining authority, otherwise report exact blocker.

If accepted, record a durable outcome and synchronize current.json. The abstract theorem status may be promoted only for this exact proposition. Original N1/O-NORM/O-RESULT/source/native/parent gates remain OPEN with source owners and missing certificates recorded. Commit only explicit coherent files, inspect the full outbound range, push non-forced, and verify remote head.

Next dispatcher consultation: this proof's frozen result or a material mathematical/dependency/resource/authority change, not internal lemmas or the commit itself.
