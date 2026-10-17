# Reduced Astra use in goal-driven sprints

Status: Draft; user has authorized this change, pending independent resource-policy review
Scope: resource policy for Astra assignments in authorized Yulang goal-driven research sprints
Approved-by: user, in conversation (“Astra使いすぎかな. なんか抑えられるようにしてね”)
Approved-at: 2026-10-17
Drafted-by: Luna primary
Reviewed-by: pending
Supersedes: the Astra per-sprint count, stage and time limits in §3 of [goal-driven-sprints.md](../../rules/goal-driven-sprints.md)

## Decision

Default to zero Astra assignments. Begin with Luna's construction or the normal
Sol/high `prover`. Use Astra only for one named core mathematical risk whose
inputs are frozen and whose bounded specialist contribution is stated in the
assignment. Astra may work at medium effort for no more than three substantive
stages and 300 aggregate seconds per sprint. The limit covers `astra_prover`,
native/model overrides, implementation escalation, all descendants and all
continuations. There is no automatic renewal, reset per stage, or substitution
of higher effort for missing inputs. At the bound, continue with Luna or Sol.
Reserve and charge the whole assignment grant when issued. If the actual
duration is UNKNOWN, or interrupted work has no confirmed writer-cessation
receipt, do not reclaim the unobserved time.

The offline sprint model defaults to zero Astra capacity. An exceptional cap
must be explicitly configured with a nonempty named mathematical risk; this
validates the recorded rationale field, while Luna still adjudicates whether
the risk and proposed work genuinely warrant Astra.

The existing one-Astra-at-a-time/global-agent, verification-process, proof
closure, exact-lease, review and runtime-receipt rules remain in force. This is a
resource-policy change only: it does not lower proof standards, promote a
conditional result, select semantics, or grant implementation authority.

## Approval context

The immediately preceding module-reference sprint assigned Astra a 1500-second
cap; exact active duration was not observed and was conservatively charged at
the full cap. The user asked to restrain future Astra use. This amendment sets a
single short exception for genuinely difficult core work while making Luna/Sol
the default. The active module-reference continuation uses no further Astra
time.
