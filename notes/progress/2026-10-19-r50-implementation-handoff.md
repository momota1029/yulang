# R50 design and implementation handoff — revision 2

Status: **PROPOSED, NOT ADOPTED; independent review pending**. No compiler slice
is authorized. Parent inference/evaluator theorem and original Simple-sub A/B
remain **OPEN, 0 -> 0**.

## Integrated proposal

The proof lane refines the design to a smaller evidence protocol than the
initial map-based sketch:

- Seal the active-local origin in the immutable source schedule: source owner,
  exact Name expression/occurrence, local and slot, initializer root, Name
  target, source-region ancestry, Link index and owning Install boundary. The
  active-map constructor must validate the exact HIR/action tuple. A
  definition-body Link gets no such origin.
- At the current Candidate action, pass an ephemeral guarded proof from the
  actual source step. It must bind the same live frame/attempt and recipe, with
  `Frame.next` at that Candidate. The successful-prefix invariant establishes
  the earlier Link ran; the exact indices must satisfy `Link < Candidate <
  Install`. Do not use a retained success map or a bare `graph.source` check.
- The scoped authenticator matches the bare Name's exact occurrence, local,
  slot, target and root to the sealed origin, verifies the active region and
  unpublished local, then admits the existing monomorphic root without a
  scheme, route, FreshUse or new root. Installed generalized locals retain all
  existing exact FreshUse checks.

This is a conditional preservation argument only. The first unsupported
premise is approval of an active-Link consumer rule without installed
`LocalScheme`/`LocalFreshRoute`; typed origin production and guarded consumption
are proposed but unimplemented. `Frame.next` alone does not prove source
authority or close alternate callers. See the frozen Sol proof for the full
premises, direct/nested application and falsifiers.

## Source/native owner map

- Producer/origin: `candidate_source::emit_candidate_source`.
- Successful-prefix/current-action guard: `step_candidate_source` and
  `execute_candidate_action`; the context must be passed through the authentic
  Candidate caller.
- Consumer: `candidate_call::authenticate_scoped_apply`, reached through
  `shadow_apply::admit_candidate_fact`.
- Install/attempt/transaction lifecycle: `candidate_scheme::GraphState` and
  `lib.rs`. Intrinsic source failure currently drops the private candidate
  session; a new retry/suspension path would need a separate attempt-freshness
  proof.

The existing active Link is an ordinary monomorphic value constraint, not a
FreshUse. The current scoped authenticator has no active-Link arm. No code,
fixtures or tests changed. The apparent scoped `execute().unwrap()` was not
executed and is not runtime evidence. R50 did not establish source typing,
`Desc`/`D_q`, full Call, effects, F1/FK1, soundness, principality, evaluator
correctness or production correspondence.

## Frozen inputs and results

- Contract rev1 SHA-256: `283f2d8abe6c62cdcaee3fd7991705b4c8a0b3dce6df4446dc204aaf4737b8da`.
- Luna's original source map and R49/authority pins were revalidated at sprint
  start; exact values remain in `current.json` and the contract.
- Sol artifact:
  `notes/theory/2026-10-19-r50-active-link-refinement.md`, rev1,
  SHA-256 `9f42dbbbf7c3e7e4d91484dc10f63026023684c6b3557d961b53399ff1b74413`.
- Sol handoff rev1 SHA-256:
  `0c3a9f14864620b9028481c851a7df680437d57cfad752bc15d15affda7cc0a8`.
- Integrated design rev2:
  `notes/design/2026-10-19-active-link-admission-r50-draft.md`.

Requested Sol/high; effective model/effort UNKNOWN/UNKNOWN. Sol grant 900 sec
charged, CPU/RSS UNKNOWN; Luna design grant 600 sec charged. No tests, build,
Cargo, runtime, Git, external contact or scratch paths. Sol writes
STOPPED/NO_DESCENDANTS. Two tracked test-only diffs and older R36–R48 artifacts
remain outside this sprint and untouched.

## Review and approval boundary

Fresh independent compiler and spec reviews must target the exact rev2 draft,
this handoff, the frozen Sol proof and both source/authority pins. They should
attack exact origin construction, guarded caller identity, transaction/attempt
lifetime, nested helper ordering, installed FreshUse noninterference and the
conditional scope. After clean review, user approval is still required to adopt
the architecture. A separate exact-path code contract is required before any
compiler change. Parent stays OPEN 0 -> 0.
