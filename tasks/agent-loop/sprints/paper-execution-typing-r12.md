# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r12 — typed-variable resume

Status: primary-owned active continuation of the user's fixed inference/executor
proof goal. Branch / baseline: `research/simple-sub-intrusion` at
`11230acfb`. Authority: `docs/yulang-operational-type-safety-ja.tex:403-405,458-465,953-977`.
R11 is frozen at `tasks/agent-loop/inbox/paper-typing-subst-r11.md`, SHA-256
`3101c2c70e7b73da63c026457b9a52f9d9eb2b48b074c745540db64fd33e0db1`.

## Fixed outcome

Change only the represented `PaperComputationTyped.resume` premise so that a
continuation is accepted through the ordinary value judgment at
`Ty.kont responseType resultType`. Keep the existing `PaperContinuationTyped`
body judgment and its constructor; keep request's canonical continuation premise,
unique operation resolution, and instance equality unchanged. This follows the
paper arm/resume interface: handler variable `k` has `Kont(Q,A)` and `Resume(k,v)`
returns `A`. Do not add handler typing, term substitution, owner renaming,
operational preservation, or new runtime semantics.

Extend the existing arbitrary-`σ` six-family transport recursor to preserve the
revised resume premise. Check the concrete distinction witness
`Γ = [Kont(Bool,Int)]`: `resume(variable 0, true)` has type `Int`; an answer at
a response type other than `Bool` must not follow. Record the exact theorem
statement and complete axiom audit. Preserve all original paper quantifiers and
keep the full typing/source/native parent OPEN.

## Exact ownership and dependencies

Primary `/root` owns:

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- this contract, `tasks/agent-loop/current.json`, and
  `tasks/agent-loop/inbox/paper-typing-subst-r12.md`
- `notes/theory/lean/.lake/R12Audit.lean` and the primary Lean/Lake cache

Read-only: `PaperTypeSubstitution.lean`, `PaperTypeFormation.lean`,
`DeclSubst.lean`, the cited paper sections, and the frozen R11 handoff. Eight
historical/foreign UNKNOWN reservations stay quarantined. No child or reviewer
is admitted; R9/R10/R11 review remains `NOT_RUN`. The Rust lane is
`NO_SAFE_CODE_SLICE`: `program.rs` and `machine.rs` do not supply a checked
source-to-this-paper-judgment bridge, and this type-rule-only change has no
production behavior authorized by its premises. Keep Rust/native and production
files out of this sprint.

Input hashes:

- `PaperExecutionSyntax.lean`: `22c2e19811d4c6a21c5b7f58d0b4c86d832031e44d53a786307453d1b8c4fba7`
- `PaperExecutionTypingSubstitution.lean`: `6893510f5b419f1d9c47bbfd26f73dbf95ccefb688ca8e74253029d2b033bbf4`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R11 handoff: `3101c2c70e7b73da63c026457b9a52f9d9eb2b48b074c745540db64fd33e0db1`

## Resources, checks, stop conditions

Maximum 600 active seconds, 6 serial Lean/Lake invocations, and 90 checker
seconds; `-j1 -M1024`, one checker at a time. R11's seven invocations and
approximately 24 seconds are already spent and do not transfer. No tests, Rust
build, default-target build, or production edit. Build the focused module and
run the exact-type/axiom audit. Stop on a type-algebra or judgment mismatch,
failed Bool/Int witness, unsafe dependency/lease, user STOP, or budget limit.
Never add `sorry`, `admit`, project axioms, checker bypasses, or assumptions
that identify response and result types.

## Acceptance and remaining boundary

Success means the revised syntax module and typing transport module build;
`resume(variable 0, true) : Int` checks under `Γ = [Kont(Bool,Int)]`; a wrong
response type is rejected by the constructor's type; all five public transport
projections and the mutual theorem print exact types; complete axiom audit has no
`sorryAx`, `_f`, failed declaration dependency or project axiom. Preserve build
failures and actual resource receipts in the one R12 handoff.

This proves only the partial extrinsic resume judgment. Full handler/attempt
rules, other omitted paper forms, term substitution, owner alpha-renaming, full
paper typing, inference/executor and original A/B obligations, source/native
correspondence, Rust bridges and independent review remain OPEN.
