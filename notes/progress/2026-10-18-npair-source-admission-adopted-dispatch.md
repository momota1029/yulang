# Post-adoption dispatch: NPAIR source admission

Authority change: user explicitly adopted the spec-reviewed concrete-only source-admission proposal on 2026-10-18. Adoption receipt: `notes/design/2026-10-18-npair-source-admission-adoption.md`, SHA-256 `fe06a42da82d9bc66da133d0266b0fa1133ffbcfb1128100377c715c0ace0d06`.

## Current gate

Admission approval is satisfied for exactly the adopted nonempty concrete-only negative formal-port source case. Original source/native parent closure remains **0**. The inherited `candidate_source.rs` / `candidate_call.rs` owners remain UNKNOWN and quarantined. No source access, hashing, write, lease recovery or new worker is authorized until actual STOP evidence plus complete descendant, generated-output and overlapping-lease accounting is recorded.

## Next source-to-proof outcome after handoff

Once Luna receives that handoff, create a fresh contract and source snapshot for a bounded audit of the normal entrypoint through parse/HIR, registration/preflight, collection/action and the reviewed `FormalAnnotation` producer. Prove the exact source owner, parameter, occurrence, scope, typed path and concrete operands are retained, with the complete Function children and links 43/44; otherwise identify the first owner-specific obstruction. Reuse the reviewed internal producer theorem without repeating it.

The implementation lane remains `NO_SAFE_CODE_SLICE` until the source audit is reviewed and an exact implementation lease is issued. Consumer, `At`/N-Ingress, transport, subtraction and all original parent gates stay separate.

No additional proposal sprint or repeated approval question adds value while the old owner handoff is missing. The dispatcher's conditional future envelope is ≤600 seconds (Luna source audit 300 + compiler review 120 + spec review 120 + reserve 60), Astra0, no build/test initially; it is not allocated or carried now. Source hashes and dependencies must be revalidated after handoff.
