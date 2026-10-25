# Declaration substitution — r5

Status: primary-authored, checked candidate; independent review NOT RUN.

## Goal and scope

Continue the full paper-first Yulang type inference and executor proof goal.
This packet proves ambient substitution for a declaration-instantiated
operation, then applies it to the declaration-derived instance relations.
It does not prove type-typing substitution, table uniqueness, nominal arity,
inference soundness/principality, executor preservation, source/native
correspondence, or either original A/B claim.

## Evidence and method

Baseline: `c9bb5e24b8b3b0f5db9cdce840359ebac8b1b100` on
`research/simple-sub-intrusion`. Frozen dependencies:

- `PaperTypeFormation.lean`: `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- `PaperTypeSubstitution.lean`: `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`

The isolated scratch candidate was SHA-256
`f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`.
It replaces the entire failed theorem proof with `operationInstance_ext`,
discharging identity, argument syntax, payload and response fields. It then
proves `operation_instance_instantiates_subst` and
`operation_instance_instantiatesIn_subst`, transporting the existential
declaration witness through mapped declaration membership.

Before checking, the source inspection confirmed that the target theorem no
longer contains `OperationInstance.mk.injEq.mpr` and applies
`operationInstance_ext`. `lake build YulangClosure.PaperTypeFormation`
succeeded, followed by `lake env lean /tmp/yulang-decl-subst-r5-scratch.lean`
with exit 0 and no diagnostics. The first scratch check had failed only because
the new dependency `.olean` files were not built; the targeted build resolved
that environment issue. The final checked source is copied verbatim to
`notes/theory/lean/YulangClosure/DeclSubst.lean`.

## Ownership, resources and review

Primary-only work; no child, reviewer, Astra, Rust, Cargo or native process was
started. Eight prior UNKNOWN reservations remain quarantined. The result is
unreviewed and does not promote any parent gate. A fresh nonauthor review must
check the complete module, the paper correspondence, and its use by the parent
typing-substitution proof before acceptance.

Exact outputs: this contract, `notes/theory/lean/YulangClosure/DeclSubst.lean`,
and `tasks/agent-loop/inbox/decl-subst.md`. Preserve r3/r4 failures unchanged.
Next: apply these lemmas to the original paper typing-substitution obligation;
name every remaining premise and keep full inference/executor/A/B open.
