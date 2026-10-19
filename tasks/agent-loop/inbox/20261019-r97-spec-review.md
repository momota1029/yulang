# R97 independent pre-edit specification review

Reviewer: fresh `spec_auditor`, independent and read-only; primary-preserved report.

**CLEAN — pre-edit specification review only.**

Verified SHA-256:

- Contract: `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce`
- Frozen `runtime_control.rs`: `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815`

Basis:

- Contract lines 10–12 match charter §21, lines 577–579: implicit and ordinary annotated parameters have Value roles; an outer computation annotation selects Computation.
- Contract lines 19–23 preserve charter §17, lines 454–460, and §21, lines 583–590: whole argument introduction is inert; Value forcing occurs within receiver activation; unused Computation arguments remain retained.
- Lines 16–19 correctly label outcomes as falsifiable candidate predictions. The effectful `signal::ping()` against `[] int` must remain a compatibility falsifier and STOP if preparation rejects it. §21 determines entry role; it does not establish acceptance of that effect/type pairing.
- Existing `runtime.rs:96–112` covers implicit Value and explicit Computation with recursive arguments, plus explicit consumption. The proposed matrix adds explicit Value annotations and effectful arguments with direct machine outcome inspection. Both suites use CandidateInference/RuntimeProgram; that path itself is not new coverage.
- Contract lines 23 and 30 protect existing expectations and exclude divergence/general theorem promotion. Finite fuel exhaustion supplies only bounded execution evidence.

Caveats: no implementation diff or proof artifact existed in this reviewed baseline. Post-freeze review must verify all six cells, unchanged existing assertions/helpers/names, and the claimed source-to-entry correspondence. Changing an old expectation would require causal authority analysis and pre-write review under `rules/testing.md`, “Expected-output protection”; changing approved semantics additionally requires user approval under `rules/design-authority.md`, “Approval and implementation gate.”

No files changed; no Git, builds, tests, or CLI execution.

## Post-freeze delta confirmation

Reviewer: same independent `spec_auditor`, read-only; primary-preserved report.

**CLEAN — specification delta; execution remains unobserved.**

Verified current SHA-256:

- Test: `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c`
- Proof: `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98`
- Proof handoff: `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb`
- Implementation handoff: `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d`

Removing the sole added test from current bytes reproduces baseline hash `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815`. Existing helpers, assertions, expectations and test names are byte-preserved.

The new test contains all six controlled fixtures. C-ping remains last, uses unchanged `machine()` preparation, and cannot mask CandidateError/conflict. Outcomes match contract lines 16–19 as candidate predictions. Roles and inspected entry branches match charter §§17/21 and runtime `program.rs:488–500`, `machine.rs:879–902,939–1009`.

The proof explicitly keeps preparation, execution and C-ping compatibility unobserved; it traces authentic formal/annotation identity through candidate formation and independent runtime entry. It preserves the distinction between bounded exhaustion and divergence and closes no parent or production theorem.

Caveats:

- The proof pins the earlier implementation handoff hash `247e66658fbf616046e4e41442f85e280213e23af508aa17f82db0e9acfbe4f3`; current handoff changes provenance reporting, while test/proof bytes remain frozen. Preserve both versions’ provenance in intake.
- The disclosed pre-edit `git status --short` violated the worker’s no-Git instruction. This is a procedural deviation, not evidence of semantic or artifact corruption; primary adjudication remains required.
- Whole-matrix success requires reaching all six assertions; any earlier failure stops execution as contracted.

No writes, Git, builds, tests or compiler CLI executed by this reviewer.
