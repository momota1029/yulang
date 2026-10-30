# R49 outcome — changes required

Date: 2026-10-31  
Sprint: `EFFECT-PERMISSION-AUTHENTICATED-RESIDUAL/20261031-R49`  
Baseline: `3b1ef27d3795b2bc56ab1718dcd3c06700699547` on `yulang3`  
Contract: `bbd29538d354355f1da604f6072544d3569887ff1fc9c0e449ec61c0afc67d9e`  
Review intake: `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-review.md`

## Result

The frozen Rust and Lean artifacts implement the bounded authenticated
residual experiment, but the independent reviewer found a blocking regression
in the known-unmatched operation case. A source Catch handling `signal::ping`
with a provider `write::ping` now becomes unavailable, although the original
behavior forwards the `write` endpoint unchanged. The cause is the assembly
pointer-equality rejection plus a planner path that tries to authenticate the
known nonmatch as a suppression candidate. The analogous partition is absent
from the Lean model. Preserve the reviewed revision as an immutable failed
submission; correct it only in a numbered successor.

The minimum repair distinguishes Match, KnownUnmatched, and Unavailable from
authenticated source identities. KnownUnmatched forwards the original endpoint
without suppression. Match can suppress only with complete R45 permission,
R47 emission, R48 arrival, and selected-arm evidence; missing evidence remains
unavailable before publication. Unknown identity never counts as mismatch.
The Lean model must prove the same forwarding witness and retain the complete
authorization condition for suppression.

The reviewer also found a minor Rust handoff revision 1 typo in the
`candidate_source.rs` dependency SHA. The actual/admitted value is
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`. Preserve
the old handoff and correct it in revision 2.

## Verification and limits

Independent review: **CHANGES REQUIRED**; no other correctness finding in the
bounded source/model mechanisms. Reviewer inspected all 23 Lean theorem roots,
types, bodies and retained final audit receipts. Complete axiom sets were
`[propext]` for three roots and `[propext, Quot.sound]` for twenty roots. No
project axiom, proof hole, or checker bypass was found. No compiler, runtime,
tests, build, or checker rerun was authorized or performed. Source extraction
completeness, concrete runtime success, Catch execution, full subtraction and
hygiene, original A/B, and production remain OPEN.

Both authors and the reviewer STOPPED. No worktree, environment, cache, target,
scratch file, or service was created. No unknown/quarantined path was read or
released. The sprint budget is exhausted; the compatibility correction and
fresh review require a separately budgeted successor packet. The R49 receipt
and this outcome are being checkpointed without staging unrelated workspace
changes.
