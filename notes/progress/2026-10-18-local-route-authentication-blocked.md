# Local route authentication sprint closeout

Sprint `npair-original-formation-and-exact-local-route-20261018`, contract rev2
SHA-256 `7dc810d4967745786b1071d58b3e2393b5c1c96169c2098de84fa039deac603f`.
Closed for resource limit with no compiler promotion. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed **0 -> 0**.

## Proof and falsification outcome

Frozen proof/decision artifacts were independently reviewed CLEAN only as a
research checkpoint. Literal disjoint-additive `Old(c) + New(q)` cannot provide
the original fixed-c action. The original identity/eliminator, universal R/W/Z
and changed-domain actions, and active-consumer reflection remain unproved.
The independent conditional one-output discriminator found no admitted source
counterexample. See the exact artifacts and review result in commit
`3ea1f69ab` and the frozen decisions in `c59ce3042`. Parent closure remains0.

## Implementation result

The candidate implemented an occurrence-indexed Local route association,
rollback/accounting, scoped-only record caps and regressions for a later local
argument plus unscoped cap noninterference. A fresh compiler review found one
MAJOR: scoped callee peeling admits Ascription and annotated local bindings,
while final authentication checks only the bare Local occurrence/slot/id/use.
Annotation-produced schemes share `LocalScheme`; full same-owner annotation
validation is absent. The reviewer found the route index and scoped-cap fixes
otherwise consistent. The author stopped at `2026-10-17 22:11:37 UTC`; no tests,
builds or fixture command ran. The `candidate_call.rs` final-authentication guard
was not applied. Nothing from this candidate is approved or integrated.

Exact unapproved source/test bytes are preserved in
`notes/progress/2026-10-18-local-route-authentication-unapproved.patch`. Final
file SHA-256 pins:

- `candidate_source.rs`: `2eb54c5a31804969a497eb2448ba9dd732dc3fc6a9d443a7b5a712c7163b7434`
- `candidate_call.rs`: `c32b97d6cd8aabfc4ff7825ee54b2c73d023898cf61d68ab218a01360eaa1469`
- `candidate_scheme.rs`: `fbe7864891afd06d6d753c54609b03d5ecea772bfe578c5b58bb19989570bba8`
- `shadow_apply.rs`: `845413605db54eb680f4293551a97cb45532cf176326109342c804475a3412e6`
- `lib.rs`: `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1`
- `tests/candidate_graph_call.rs`: `4214096b11aa087e4d94a2d0b40a15b40f5466d5148ed23265ebc79d8a7cc597`

The frozen reviewer receipt is the final result in `/root/npair_exact_local_route_review`;
its six reviewed hashes are in sprint rev1/rev2 history. Fresh review required
after the repair. No resource rolls forward.

## Resource/next action

Sprint rev2 total cap was2460s; proof600s, falsifier300s, implementation1020s
including360s verification reserve, proof review180s, compiler review240s,
primary120s, contingency0. At stop the author estimated about225s total
remaining after the +60 transfer, less than the protected360s verification
reserve. Even adding the entire primary120s yielded345s; dispatcher declined
additional edits, reduced verification, or exceeding the cap.

Successor proposal: `npair-local-route-authentication-and-runtime-20261018`,
with a fresh2100s cap, an integrated source/call/shadow authentication proof,
fresh compiler review and the original two-command verification after CLEAN.
The source/theorem blockers above are inherited unchanged; no semantic owner
input arrived. Preserve Astra0 and the original theorem quantifiers/domain.
