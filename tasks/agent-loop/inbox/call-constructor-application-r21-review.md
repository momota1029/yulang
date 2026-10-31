# CALL-CONSTRUCTOR-APPLICATION-R21 — independent review intake

Assignment: fresh independent `compiler_referee` review of the frozen R21
contract, manifest, proof note, and both lane handoffs. Reviewer: `/root/r21_independent_review`.
This file records the reviewer's returned verdict verbatim in substance; the
reviewer did not write the file because its governing role is read-only. Luna
materialized this primary-owned intake record from the completed review result.

Verdict: **ACCEPT — conditional missing-premise receipt only.** No blocking,
major, or minor correctness findings within the admitted scope.

## Reviewed evidence

The reviewer reports that all five assigned hashes, all 19 direct manifest
hashes, and all 25 nested R20 pins matched. The reviewer did not inspect
excluded sources or current Rust working-tree substitutes, and ran no
compiler, test, Lean, Git, or file-writing operation.

Independent direct-owner checks support the conditional result:

- `OriginalSourceGeneration.lean:63–74,111–124`: `f 1` generates the five App
  obligations; literal argument `1` cannot satisfy the restricted Name/Name
  singleton Role₀ branch.
- `OriginalSourceEnvironment.lean:163–178,557–562`: registration determines
  the callee-returned-value subject; it supplies no complete Call typing.
- `SourceSignatureConstruction.lean:587–592,639–646,711–730`: installation
  supplies static incidence, preserves registration/substitution, and retains
  six ordered regions plus all arms.
- The selected complete-Call definition §§2–5 and interface definition §§2–4
  support the displayed conditional composition. Authentic Q, independent
  complete C0, matching O1, and the actual IF contract envelope remain separate
  requirements.
- Frozen `candidate_scheme.rs:967–1129` confirms positive selection fails for
  zero or multiple matching nodes. Later typed replay port checks remain
  unexecuted. `candidate_context.rs:3085–3201` and `shadow_apply.rs:4130–4168`
  preserve `(argument, argument_effect, result_effect, result)`.
- `OriginalSourceGeneration.lean:1026–1031` requires full semantic `Satisfies`;
  native success alone supplies neither this premise nor `sameScoped`.

R21 correctly stops at the absent aligned authentic operation and independent
C0, with additional O1/IF/native ownership cuts identified. It neither masks
the selector symptom nor proposes an unsupported repair. Parent theorem,
source/native, effect-hygiene, and production gates remain **OPEN**.

## Runtime receipt

The review result arrived through the isolated reviewer assignment and is
independent of the proof and implementation authors. Requested role:
`compiler_referee`; effective model/effort, launch anchor, elapsed time, and
remaining budget are **UNKNOWN**. No file write by the reviewer occurred.
