# Receipt: native ordinary Direct consumer architecture

Question ID: `native-direct-consumer-architecture`
Question revision: `q1`
Approved draft: `native-direct-consumer-architecture-answer` revision `d1`
Approved answer SHA-256: `5b836d245eba2faff163b0c6ef7f92ebfff05b68ddd522d3d033bb2b7687558c`
Question bundle commit: `852f70117`
Validation date: 2026-10-08
Outcome: accepted and integrated

## Validation evidence

- Question/draft IDs and revisions match q1/d1, and the embedded approved
  draft is byte-for-byte equal to the current `answer-draft.md`.
- The approved answer records explicit user approval `「OK」` after d1 was
  displayed and selects option 1 only.
- The reviewed proposal hash is
  `1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60` and
  still matches `notes/design/2026-10-08-native-direct-consumer-plan.md`.
- The matching question, approved current draft and approved answer were
  committed together in `852f70117` and pushed to
  `origin/research/simple-sub-intrusion`.

## Application and remaining scope

Select the flat-arena proposal as the architecture direction for a checker-only
gate for supplied native ordinary `Direct` proofs. The next authorized design
work is to map exact caller and local-law owners and choose numeric resource
limits before implementation. This does not authorize implementation, a public
API, source semantics, inference routing, production use or F5 replacement.

Next: finish the caller/local-law owner map and bind finite limits to the
supported caller envelope. Preserve the proposal's stated failure modes and
one-compilation shared budget. No implementation may begin until those design
prerequisites are reviewed and recorded.
