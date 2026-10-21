# R239 — Parent instance mapped-bound admission

Status: active source/proof audit; no result frozen.

## Fixed obligation

The parent is `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7 (SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`). Its direct-Name template has original admitted constraints `e_t<=e_n<=e_R` and `e_n<=e_t`. For one authentic FreshUse instance map `mu`, the parent implication additionally requires the mapped bounds `mu(e_t)<=mu(e_n)<=mu(e_R)` and `mu(e_n)<=mu(e_t)` to be actually admitted, together with actual Apply argument/output and next-provider joins. This does not assert that a solver RelationId is itself a `mu` image.

R238 established that a raw `Work::Bound` transfers exactly the fibers at its physical raw key; equality canonicalization does not reverse-attach children to stale raw keys. It did not establish whether a parent-required mapped bound uses that route. R71/R72 and the parent remain OPEN.

## R239 question and method

For the direct-Name provider-use base case, can each source-labelled original inequality be followed through actual emission, authentic capture, one consistent FreshUse map, successful restoration/replay, admission/activation, and the actual Function comparison? Keep Module and retained Local routes distinct. If a step is absent, identify the earliest missing constructor/admission premise and the source/native owner. Only invoke R71/R72 if the parent-required mapped bound is shown to depend on its canonical-child route.

The audit uses the frozen contract `tasks/agent-loop/sprints/simple-sub-parent-instance-admission-20261021-r239.md`; its SHA-256 and exact source inputs are frozen at sprint start.

## Evidence and result

Pending. No implementation change, test, build, or sample execution is authorized by this packet.
