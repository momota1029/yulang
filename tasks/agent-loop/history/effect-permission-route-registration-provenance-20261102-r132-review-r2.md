# R132 independent review receipt — handoff revision 2

Verdict: **PASS for the bounded source ownership/provenance repair, with one
MINOR correction to the failure/publication description.** No blocking or major
source issue found. This receipt narrows the earlier R1 result to the reviewed
R2 candidate; R1 remains an accurate historical failure for its different
bytes.

Reviewer: `/root/r132_r2_independent_review` (`compiler_referee`), read-only,
STOPPED. Handoff: 27,796 bytes, SHA-256
`ca764276988f958f2799b5eafef1d3f3002cd7730ec5aed18bcfe82b38e747a1`.
Contract SHA-256:
`ba88ab578b9a851181eb603283fc80823eab7f4ed0b878df2103e1faa6a2519e`.
The reviewer independently matched all nine committed source pins and
reconstructed the 508,255-byte candidate at SHA-256
`9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`.

## Accepted bounded findings

R2 passes `&origin.lambda`, borrowed from the same session-owned context origin,
to the permission binder. This avoids returning a permission view tied to the
local `native` value that is moved into the tuple. Registration and Lambda
identity are checked before the borrow. For row consistency, the adapter
compares current representatives of the selected incidence's captured graph
row and raw source row. Structural registration/incidence still selects the
permission; row equality is only a consistency check. The patch context,
closing braces, signature, feature gates and field visibility appear
statically plausible.

The review attacked two Lambdas sharing row/Function values, missing or
duplicate origins/recipes/permissions, source occurrence/formal mismatch,
repeated route selection and representative changes. Existing Function,
child-1, mapped Effect row and permission guards remain. The adapter has no
consumer.

## Minor receipt correction

The R2 handoff overstates route atomicity by saying a FreshRoute remains
unpublished until the enclosing operation completes. In the pinned baseline,
`candidate_scheme.rs:4880` appends the route before fallible obligation
retention and resource sampling at `4889–4903`. A failure can therefore leave
a transaction-local route temporarily present; `lib.rs:9746` restores
intrusion state and `lib.rs:9766` truncates routes during rollback. Read the
phase boundary as: completed FreshUse construction can be retained temporarily
inside the enclosing route transaction; successful transaction completion
makes it durable; failure rollback removes that temporary route and restores
intrusion state. Any future consumer must respect this boundary. This is not
an active acceptance bug because the new adapter has no consumer. The frozen
worker handoff remains unchanged; this primary receipt supplies the correction.

A prior dispatcher note appeared to say the pinned scheme baseline lacked
capture/FreshUse propagation. Luna checked the exact pinned commit
`559021b7157b5f1fea949d08228aad13171d07b8`: `LambdaArgumentEffectCapture`
and `LambdaArgumentEffectFreshUse` are declared in `candidate_scheme.rs`,
capture reads context origins at lines 2875–2897, and FreshUse maps retained
incidences at lines 4442–4458. The note was stale for this baseline.

## Limits and gate status

No compiler, Cargo, tests, Lean, checker, storage/environment probe, scratch,
source materialization or runtime execution was performed. Compilation remains
unverified. This review does not close consumer correspondence, Rust-to-Lean
correspondence, the original A/B claims, effect hygiene or production
readiness. The source candidate is an additive provisional adapter only.
