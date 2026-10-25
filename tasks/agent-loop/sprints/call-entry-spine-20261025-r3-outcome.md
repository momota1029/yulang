# LEAN-CALL-ENTRY-SPINE-20261025/r3 outcome

Status: **ACCEPTED / CLEAN**, syntax-typing milestone only. Integrated by Luna.

## Fixed claim and result

The exact `completeCallEntry_typed` proposition in the frozen r3 contract
compiled without changing its hypotheses, existential witnesses, arbitrary
pending-adapter suffix, or conclusion. The composition imports the frozen P
and Q modules and reuses the outer existential `consumer` in both dependent
branches, correcting r2's branch-local identifier elaboration failure.

P proves typing of the call-entry body for both modes; Q proves structural
peeling existence and typing preservation for arbitrary pending adapters.
Composition combines those exact results. The checked declarations and trust
boundary are recorded in the verification receipt. A fresh nonauthor reviewer
returned CLEAN with no blocking, major, or minor findings.

## Evidence

- Frozen contract: `tasks/agent-loop/sprints/call-entry-spine-20261025-r3.md`,
  SHA-256 `e331976b445955fa6e982427287494772bc8a823b706f460291c91d4078d4928`.
- P source `CallEntryTypingRepair.lean`, SHA-256
  `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39`.
- Q source `CallPeelingTyping.lean`, SHA-256
  `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`.
- Composition source `CallEntrySpineComposition.lean`, SHA-256
  `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf`.
- Verification JSONL:
  `tasks/agent-loop/inbox/20261025-call-entry-spine-r3-verification.jsonl`,
  SHA-256 `65c5d0b7319b4c9bced1fca11e7bc20060842d4e66aaa02e84706229b720d2eb`.
  It contains the accepted P/Q artifact reuse record and exactly two successful
  Lean invocations: composition compile (exit 0, 0.220242 s) and exact query
  (exit 0, 0.206938 s). The query prints all five requested signatures and
  axioms: `[propext]` for P and composition; none for Q existence, delayed
  argument typing, or Q preservation.
- Frozen independent review:
  `tasks/agent-loop/inbox/20261025-call-entry-spine-r3-review.md`, SHA-256
  `1c6bfc4f5dfa140c8d571fe88edd6302a7e184dce0d5e7feb4f07d7385a93a37`.
  Reviewer `/root/call_entry_spine_r3_review` STOPPED after a read-only CLEAN
  audit. Effective model and effort remain UNKNOWN.

## Scope and remaining premises

This closes the exact syntax-typing composition theorem under the accepted
Lean environment. It does not prove operational Call A/B, source/native
correspondence, execution or effect preservation, inference A/B, or production
readiness. Those parent gates remain OPEN. The result is not evidence that
runtime source constructors realize the relation.

## Changed paths and integration

The accepted composition, complete Lean receipts, independent review report,
this outcome, and compact current-state closure are integrated together.
P and Q were already frozen and tracked by the prior checkpoint. No Rust source
or tests changed. The three historical UNKNOWN reservations remain
quarantined. The outgoing range was inspected and pushed without force.

Git integration locator: the commit that first introduces this outcome file;
resolve it with `git log --follow -- <this path>`.
