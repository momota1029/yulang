# R16.2 primary final audit receipt

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r16`, contract amendment `paper-execution-typing-r16-rev3.md`, SHA-256 `4a2d37ba591815ce2d824ca62152980b769dffafea2d424b0853ae164236faee`.

## Frozen inputs

- Proof source `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`, SHA-256 `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`.
- Worker handoff revision 2 `tasks/agent-loop/inbox/paper-typing-subst-r16.md`, SHA-256 before this receipt `77df07e5f7f8cf6dd9e4caf228da857b5c450fe217534faba8d552145478bf39`.
- Import audit scratch `notes/theory/lean/.lake/R16Audit.lean`, SHA-256 `905385495f1a0fcdcc76961af2ecf2b365eac72470af6b81a605b7d703530d77`.
- Pinned toolchain: Lean 4.35.0 (`leanprover/lean4:v4.35.0`).

## Primary-owned final calls

Call 11: from `notes/theory/lean`, ran

```sh
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperExecutionBinderLaws
```

Exit 0, 5.53 seconds, build completed successfully (6 jobs). Existing linter warnings were emitted, chiefly unused variables/simp arguments; no errors occurred.

Call 12: from `notes/theory/lean`, ran

```sh
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R16Audit.lean
```

Exit 0, 0.15 seconds. It printed 22 exact theorem types and complete `#print axioms` results, including all 14 new public syntax/template/declaration commutation laws. Each of those 14 reports `[propext, Quot.sound]`; the six prior substitution/binder helpers and two environment commutation laws also report `[propext, Quot.sound]`, except `liftSubN_add`, which reports `[propext]`.

Worker call 8 separately printed 28 complete theorem-type/axiom pairs, including private mapping helpers and the common `shiftAt_all` induction. The complete lists are preserved verbatim in the worker handoff revision 2. `liftSubN_add` alone uses `[propext]`; the other 27 use `[propext, Quot.sound]`. No `sorryAx`, failed declaration dependency, project axiom, native-evaluation assumption, or unapproved axiom appears. Source/scratch/handoff hashes were rechecked against the worker's frozen receipts before the final calls.

## Result and limits

R16's nine-family raw syntax shift/substitution commutation and the `TemplateBody`, operation, nominal-constructor, primitive-signature and complete declaration-table applications have passed construction, focused module build, and import-based type/axiom audit. Every constructor and actual executable template code remains in scope. Calls 1–8 and primary calls 11–12 are charged; worker calls 9–10 remain unused and are not transferred. The original active-time and checker-time caps were not reset.

This receipt is not independent review or Luna adjudication. Review remains `NOT_RUN`; the proof artifact is `FROZEN_AWAITING_REVIEW`. The theorem is a raw mapping prerequisite only. Six-judgment binder weakening/reindexing, shared-environment freshness and value-only forall introduction remain the first parent seam. Full typing substitution, execution safety, inference soundness/termination, original A/B, source/native/Rust correspondence and production authority remain OPEN.
