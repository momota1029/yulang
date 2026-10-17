# Frozen Catch metadata read/exit correspondence handoff

Sprint: `catch-raw-answer-and-metadata-read-20261017`, contract revision 1,
SHA-256 `16c4ea4b8bd3ace3d11b0066eb1e32955f20358d14fe94d455f516269244f800`.
Assignment: `CATCH-META-EXIT-COMMUTE-1`; handoff revision 1.
Parent: original FORWARD-FIRST-CALL A/B, F1/FK1 and
`CATCH-EXIT-INPUT-1/M_exit`; every gate remains OPEN.
Baseline: source pin set in contract; author started at primary record
commit `be2ff0460` after the Astra proof writer stopped.

## Outcome and parent application

Static source/consumer correspondence only. The current runtime does not
directly commute a full pre-pop `PendingRequest` metadata read to the proposed
post-exit `InspectRequest_μ`: capture stores declaration and event ID on the
continuation-template branch, and ordered suffix frames; it does not store
payload, observation vector or request source. The fixed Unit arm creates no
payload binder. No full historical metadata tuple is available to the selected
post-pop arm through the inspected path.

This is not a source semantic counterexample to the Draft. It records a missing
runtime producer/consumer bridge. Pre-pop validation and grants remain at their
current phase; no historical eligibility is transported as post-exit
authority. Full source/native and all original theorem parents remain OPEN.

## Artifact and provenance

Artifact: `notes/theory/2026-10-17-catch-metadata-read-exit-commutation.md`.
SHA-256: `6266619dddfc13431ed389f44824965362a47bdf9a9f9050ad672c267306089c`.
Sole author: `/root` (Luna primary); no descendants or coauthors.
Requested/effective model metadata: Luna primary / gpt-6.1-sol high configured;
runtime-observed model metadata UNKNOWN. Work was static read-only source
inspection plus authoring; no tests, builds, runtime, network or code edits.
The artifact distinguishes retained refs, absent fields, capture-only branch,
and owner/eligibility phase. No scratch paths.

## Direct dependency verification

Before reliance and at freeze, recheck all pins in
`tasks/agent-loop/sprints/catch-raw-answer-and-metadata-read-20261017.md`.
The source owner hash set is unchanged. The direct code owners used were:

```text
b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
6fb1fa9844b98fb8173d2faef2c609e35ea65248d78bf193c39ab7a85cee00d4 notes/design/2026-10-17-catch-matcher-target-declaration-proposal.md
6a86f684b0dfd879cc0a14addea293b2bde2766edd53829c2404a4290397de03 notes/theory/2026-10-17-catch-target-response-answer-instantiation.md
```

## Exact next owner and review

The runtime has no post-pop consumer for the complete q tuple. A next source
author must define where the event/declaration/payload/historical evidence
operand survives the admin exit, while separately proving that it neither
reinstalls H nor turns historical observation into current eligibility. That
requires a new exact source/rule review and remains distinct from the
ApplyOne `d_B(τ)` admission gap.

Fresh independent review of this frozen artifact is pending Luna. The current
compiler_referee review is assigned only to the separate frozen ApplyOne proof
artifact; it must not certify this note. Both writers are stopped before Git
integration.
