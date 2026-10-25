# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r11 — continuation/request/resume

Status: issued by the primary for the continuing full inference/executor proof goal.
Branch / baseline: `research/simple-sub-intrusion` at
`46ff3a262` (R10 pushed checkpoint). Authority:
`docs/yulang-operational-type-safety-ja.tex:345-359,458-465,953-977`.
Preserve the original simultaneous-substitution claim and all paper/source
obligations.

## Fixed outcome

Add the actual paper type constructor `Kont(Q,A)` to type syntax, mapping and
substitution, and type formation. Do not encode it as `callable` or erase the
distinction between operation response `Q` and normal result `A`.

Add `PaperContinuationTyped D Xi Γ K Q A` to the mutual typing judgments.
A continuation body is typed at `Q :: Γ` with result `A`; owner binders remain
owner/handler names and do not bind graph/resource identities. The existing
`GraphEnvironment` represents the paper's `Xi` and must be shared unchanged by
every premise. Add request typing using one uniquely resolved operation
declaration and the same instantiated operation instance for payload and
response, plus a continuation typed at that response and producing the request's
normal result. Add resume typing from that continuation and a response value to
its normal result. Keep arbitrary `σ : Nat → Ty`.

Extend the six-family transport proof by the explicit mutual recursor. Reuse
R10 declaration-resolution preservation and operation instance commutation.
Type substitution preserves owner binder names; this packet does not claim
capture-avoiding owner renaming or raw resume renaming. Do not add operational
step preservation or handler-arm typing.

## Exact ownership and dependencies

Primary `/root` owns:

- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- this contract, `current.json`, and `tasks/agent-loop/inbox/paper-typing-subst-r11.md`
- the primary Lean/Lake cache and checker

Read-only inputs: `DeclSubst.lean`, the paper, and frozen R10 handoff. The eight
historical/foreign UNKNOWN reservations remain quarantined. No worker or fresh
reviewer is admitted; the implementation lane remains `NO_SAFE_CODE_SLICE` and
Rust/production code stays out of scope.

Input hashes at issue:

- `PaperTypeSubstitution.lean`: `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`
- `PaperTypeFormation.lean`: `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- `PaperExecutionSyntax.lean`: `58f817365d47cfaca9f66ab8506b03d7b56efe854514e67f1669c94580d11141`
- `PaperExecutionTypingSubstitution.lean`: `54eb18f8a3a9c4ac0d28d99cf75a77032f6caf9b082832e651d3de12cbe84c79`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R10 handoff: `bd2bf59aeee4b0420e88dfdc97fbc4fc13f2a5b61def242206f954aa862fd055`

Budget: at most 900 active seconds, 8 serial Lean/Lake invocations, and 120
checker seconds; `-j1 -M1024`, one checker at a time. All R1-R10 charges remain
recorded. Stop at a concrete mutual-index/type-algebra obstruction, a
counterexample, authority/dependency change, user STOP, or budget limit. Never
use `sorry`, `admit`, project axioms, tests, Rust/native builds, or compiler
changes.

## Acceptance and remaining boundary

Success requires a normally building focused module; exact types and complete
axiom audits for `Kont` substitution/formation support, continuation
transport, request/resume transport, all existing five judgment transports,
and the R10 instance/resolution dependencies. No `sorryAx`, `_f`, failed
declaration dependency, or project axiom. Explicitly map which paper rules are
represented and still omitted.

R9/R10 reviews remain `NOT_RUN`; no self-review counts as independent. Full
paper typing, handler arms/attempts, owner alpha-renaming, term substitution,
inference/executor soundness, original A/B obligations, source/native
correspondence and Rust bridges remain OPEN. This slice adds typing forms only;
it proves no runtime transition preservation.
