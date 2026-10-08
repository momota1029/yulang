# Receipt: owner of the authentic initial JointWF context

Question ID: `l4-initial-jointwf-owner`
Question revision: `q1`
Approved draft: `l4-initial-jointwf-owner-answer` revision `d1`
Approved answer SHA-256: `3e7e520a29818c105bca09f8c46c44e6d1cc2562c5d973580491bbc552e99da2`
Question bundle commit: `9598eee7a`
Validation date: 2026-10-08
Outcome: accepted and integrated

## Validation evidence

- `approved-answer.md` question/draft IDs and revisions match q1/d1.
- Its embedded approved draft is byte-for-byte equal to the current
  `answer-draft.md`.
- The answer records the explicit user approval quote `「OK」` after the d1
  draft was displayed, and authorizes option 1 only.
- The selected source proof SHA-256 is
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; the
  L4 source trace SHA-256 is
  `f9b6d30855f26d9e87cd9f64aa23c46957c74ff042c2a9d0bbddb48f98a501f5`.
  Both match q1. The cited HIR/solver entrypoint paths are unchanged from the
  recorded source revision.
- The matching question, approved current draft and approved answer were
  committed together in `9598eee7a` and pushed to
  `origin/research/simple-sub-intrusion`.

## Application and remaining scope

Caller ownership of the authentic initial `JointWF` registry/scope/authority/
incidence context is selected, with incremental compilation as the stated
rationale. This resolves the producer-owner question only. It does not define
the Rust API, evidence validation, storage/lifetime, versioning or invalidation,
nor authorize compiler implementation or cutover.

Next: produce a reviewed durable context-input contract covering complete
evidence and dependencies, validation and lifecycle before implementing the
caller seam. SourceBuild freezing and other dependent work continue to require
their own genuine local-law and source/HIR correspondence suppliers.
