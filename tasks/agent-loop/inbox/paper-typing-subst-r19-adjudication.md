# R19 primary adjudication — wrap typing and arbitrary substitution

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r19`, contract r1 SHA-256
`3f0448e72500adab70e0fa0890aee0c5641032b77dfedf6714bd270d95c6fc74`.
Baseline `c5d41edcbd5689f0c4365a0b5330b709fed422ee`.

## Disposition

**R19 accepted as a reviewed prerequisite.** Under `YulangClosure.PaperTypes`,
the represented judgments now include `PaperValueTyped.wrap`, a genuine
`PaperValueTyped.wrapInversion`, and `PaperComputationTyped.callWrapped`. The
common arbitrary-σ substitution proof handles the new wrap case, preserving all
six transport theorem statements and their existing constructors/premises.

The rule follows manuscript `docs/yulang-operational-type-safety-ja.tex:224`
exactly: the function has `callable A B`; the argument adapter has result `A`
under `A' :: Γ`; the result adapter has result `B'` under `B :: Γ`; and the
wrapped value has `callable A' B'`. The wrapped Call consumes a thunk of `A'`
and returns `B'`. The original full-paper typing/substitution parent remains
OPEN. R18's unresolved `R18-VARIANT-TYPEARG-CORRESPONDENCE-1` remains OPEN and
is not resolved or consumed by this packet.

## Frozen artifact and independent review

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256
  `2192b5de98b9af217318dd95db93c6fd4b776e93266f62ec7e4e23402166acb3`.
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`,
  SHA-256 `6c41d59cf9326b2e94e612b62c02448991979d60658a88a001a4e7143bbfefdc`.
- Worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r19.md`, SHA-256
  `d014f09205bb2c08af78c656d476035ae25e8b08b1590f3dc01d88469924c65e`.
- Audit source `tasks/agent-loop/inbox/paper-typing-subst-r19-audit.lean`,
  SHA-256 `d6f4ea5cb8206784ef0794007adc207331738a2157df7c9def803c60ee4c0263`.
- Primary final audit output `tasks/agent-loop/inbox/paper-typing-subst-r19-primary-audit.txt`,
  SHA-256 `75913eeec8a8e5a63990d237e48ef8d780d5b5f4da66b6685aa8af21ac75c84c`.
- Fresh non-author source-only review
  `tasks/agent-loop/inbox/paper-typing-subst-r19-review.md`, SHA-256
  `89ff4b6f2252669a5755161061452487f65d7c1b95e7cc8484b664e5f152dd91`.
  Verdict: no blocking or major findings. The reviewer checked manuscript
  correspondence, both adapter directions/contexts, inversion, wrapped Call,
  all six transport statements, dependencies and axiom reports. Review used
  zero Lean/Lake calls and is not a fresh kernel receipt.

## Checker receipts and limits

- Worker invocation 1: focused build of `PaperExecutionSyntax` and
  `PaperExecutionTypingSubstitution`, exit 0, 23.970148 sec.
- Worker invocation 2: `lake env lean -j1 -M1024 .lake/R19Audit.lean`, exit 0,
  1.993374 sec. The eight audited theorems each report exactly
  `[propext, Quot.sound]`; the `PaperValueTyped.wrap` constructor reports no
  axioms. No `sorryAx`, project axiom or failed declaration appears.
- Primary invocation 7: repeated focused build, exit 0, tool-reported process
  wall time 0.427718 sec. The tool response's verbose warning output was
  truncated in its display; the visible diagnostics are existing unused
  binder/simp-argument linter warnings. The worker's retained full invocation-1
  output also ends with successful build completion.
- Primary invocation 8: repeated exact type/axiom audit, exit 0. Full output is
  retained in the primary audit log above. Its process wall time was not
  captured separately; it completed within the configured 30-second tool wait.
- Total: 4 of 8 permitted Lean/Lake invocations, 25.963522 exact worker checker
  seconds plus 0.427718 seconds for primary call 7; primary call 8's exact
  elapsed time was not retained and is below 30 seconds. Thus measured checker
  time is below 56.391240 seconds of the 120-second cap. Calls 3–6 were unused;
  no budget transfers. Active-time telemetry is unavailable.
- All six frozen dependencies and the manuscript hash match the R19 contract.
  No frozen dependency changed. Worker cessation was confirmed: writes stopped,
  with no processes or descendants.

## Scope that remains open

This result adds only the represented wrap typing rule, its inversion, the
stated Call typing derivation, and their arbitrary simultaneous substitution
support. It does not prove wrapped-Call operational preservation, any machine
transition, inference or executor safety, source/native or Rust correspondence,
the original A/B claims, production readiness, or all-manuscript rule coverage.
Variant, nominal, switch, remaining omitted forms, recursive graph guards, and
the full paper parent remain OPEN. R18's separate typeArguments authority gap
remains explicitly OPEN.
