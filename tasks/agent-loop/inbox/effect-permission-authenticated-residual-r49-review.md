# R49 independent review — frozen intake

Reviewer: `/root/r49_review`; independent of both authors. Both authors were
confirmed STOPPED before review. The reviewer returned this report read-only;
this primary intake preserves the complete adjudicated finding and the final
audit census. The full reviewer response remains in the conversation record.

**Verdict: CHANGES REQUIRED.** One blocking compatibility regression and one
minor provenance typo. No compile, runtime, production, or parent-theorem
success is certified.

## BLOCKING: known nonmatching Catch operation rejects instead of forwarding

In `crates/yu-solver/src/candidate_receiver.rs`, `assemble` at the reviewed
lines 772–774 requires `Arc::ptr_eq(handled, operation)`. The existing
regression witness at lines 1163–1189 has a `signal::ping` Catch arm and passes
`write::ping` to the relay. The declarations are different, so assembly returns
`Unsupported` before a residual plan exists. The admitted pre-R49 source
transcription retained `selected: handled.id == operation.id`; false remained
available and the provider endpoint was forwarded. The regression is therefore
an observable behavior change: an annotation permission does not close the row,
and the `write` effect must remain outward.

Removing only the pointer-equality guard is insufficient. The planner around
lines 880–898 treats the provider member as a suppression candidate and rejects
when `selected_arm.matches_provider` is false. The implementation must retain
authenticated source evidence for both resolved identities. A known mismatch
must disable suppression and forward the original endpoint. A matching arm
still requires complete permission/arrival authentication and fails closed if
that evidence is missing. Unauthenticated or ambiguous identity remains
unavailable; it must not be called a mismatch. Names, families, or pointer
inequality alone cannot establish this classification.

The Lean model has the same missing partition: `providerCandidate` and
`decideEndpoint` route a known nonmatch through authentication, and the current
model does not prove the source witness forwards. It must model Match,
KnownUnmatched, and Unavailable, with a constructive witness showing the
original endpoint survives the fold and the existing full-authentication
condition for every suppression.

Required fresh attacks: the signal Catch/write provider witness; same-spelling
distinct declarations; matching operation with missing permission/arrival;
unknown identity; authenticated matching suppression; and same-family sibling
preservation. Preserve the existing source expectation and complete-plan-before-
publication order.

## Minor: frozen dependency hash transcription

Rust handoff revision 1 records a malformed `candidate_source.rs` hash. The
correct actual and admitted hash is
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` (the
handoff omitted the `7` after `...870bfd`). The source matches the contract;
this is a receipt transcription error. Preserve revision 1 and correct it in a
numbered handoff revision 2.

## Other reviewed properties and proof census

The reviewer found no additional correctness issue in typed `SupportMember`
steps, closed-tail/member checks, actual Catch-arm source evidence, physical
path ownership, full-plan-before-publication, exact forwarding endpoints, or
same-family sibling handling. These findings do not override the blocker.

The reviewer inspected all 23 Lean declarations, bodies, final types and audit
receipts. Complete transitive axiom sets were `propext` alone for
`support_member_sound`, `lower_path_arrival`, and `fold_correspondence`; the
other 20 declarations reported `[propext, Quot.sound]`. No project axiom, proof
hole, or checker bypass was found in the inspected dependency cone. Final audit
9 input SHA-256 was
`258a3953b6a4ded5ef919db873f3e61a043e8d4e2490a6e8365a747893818cb6`; stdout
SHA-256 was
`783734242d3e6a3649423a86cd026ec42697474bd4edb101176b8b18d03f0e75`. These
are retained producer receipts, not a reviewer rerun.

Frozen inputs independently read by the reviewer:

| Artifact | SHA-256 |
|---|---|
| Contract revision 1 | `bbd29538d354355f1da604f6072544d3569887ff1fc9c0e449ec61c0afc67d9e` |
| Admission | `fe90989cbce2bbd86518eceb14920ecbffa221933399704473dbb94f2fd5bcce` |
| Rust source | `4be3a60b382c9b294893e9a41c24818ad37aea8ed7ae4f9d337ce1f50fc9b7b3` |
| Lean module | `ba9800813d2b005ec023971ac88798e1b4e41f2a93b971ddc025d8985c844ce0` |
| Rust handoff revision 1 | `aa9f7a2c28615850a4f78dcd6f35d38725e8a2a1104265f89e37506a2f9b8ae7` |
| Proof handoff revision 1 | `90bb99675de20fe8cf58c41fb14b7366f83eea2cd7487c0ba2fbf87419a85e71` |

Open after this bounded review: Rust/HIR extraction into Lean tables, branded
identity and same-state lifetime interpretation, terminal traversal
completeness, native execution/allocation behavior, Catch execution, complete
subtraction/hygiene, original A/B, soundness, principality, termination, and
production. Reviewer STOPPED; no writes, builds, tests, checker reruns, Git,
scratch, cache, target, environment, or quarantined-path access.
