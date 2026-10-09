# Candidate closed-finalization dependency: next gate

Date: 2026-10-10
Inspected committed baseline: `29f645c56d62cd18ae15557ca612c52c549fb620`
Status: architect-confirmed private lifecycle refactor; implementation pending
Authority: [active legacy withdrawal](../design/2026-10-10-simple-sub-legacy-withdrawal.md)
Mode: M2 implementation gate; semantic and regression reviews, zero measurement budget

Graph execution already bypasses F5 scheme installation and ordinary incoming
uses already recapture/freshen live roots. Candidate startup nevertheless creates
`ClosedTypeFinalizationSession`, and candidate finish consumes it. The shared
`SolvedModule` shell has closed-result accessors which assume finalized scheme
slots. These are obsolete candidate lifecycle dependencies, not complete Call
or public scheme obligations.

The confirmed repair belongs to result ownership:

- Keep public `SolvedModule` and historical `CandidateValueObservation` as
  legacy closed-result owners.
- Introduce a private `CandidateSolvedResult` owned by `CandidateInference`;
  share actual common execution/finish data and retain candidate graph/Call inputs.
- Use explicit private candidate startup/run/finish paths which never construct
  or finish a closed finalizer, receipt or closed scheme.
- Narrow `candidate_call::observe` to its actual borrowed HIR, store and retained
  Call inputs rather than requiring a legacy `SolvedModule`.
- Preserve existing candidate export/conflict/Call observations and foreign-root
  checks. Closed observers remain attached only to the legacy result capability.

Do not fill missing closed slots with empty placeholders. Preserve common
store/error/projection accounting; transfer actual candidate owners and release
temporary solver storage on finish. Startup/finish failure publishes no result.
Resource terminal assertions must describe the actual owned payload, not require
a fictitious closed arena.

Focused guards must demonstrate zero candidate finalizer construction/finish,
independence from an injected unused legacy-finalization failure, preserved
candidate observations and foreign-root rejection, unchanged ordinary/historical
F5 behavior, and correct ownership release on failure/drop.

Current private snapshots are not transformed public schemes. They omit the live
levels/metadata and older-anchor bounds needed for an independent post-finish use.
The [approved public-root policy](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md)
still requires displayed schemes plus justified additional information without
renaming the full source relation or consulting the original definition at use.
This lifecycle gate does not close that requirement, complete Call, hygiene,
soundness, principality or production cutover.

Implement after the moving concrete/co annotation repair freezes and integrates;
the shared solver paths require serialization. No code, test or measurement ran
for this read-only mapping. No new user decision was identified for removing the
unused private runtime prerequisite.
