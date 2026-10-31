# R120 independent review — primary-recorded reviewer report

The independent `compiler_referee` completed a read-only review. Its role forbids writing files, so the primary recorded the received report here; the reviewer did not author this file. The reviewer authenticated the frozen inputs and independently reconstructed the composition before reading the implementation handoffs.

## Decision

**PASS for research records only; `NO_AUTHENTICATED_TRACE` upheld.** No new blocking, major, or minor defect was found. Source integration, Rust compilation, Lean acceptance and parent theorem closure remain unestablished.

## Authenticated inputs and composition

- Contract SHA-256: `85246d529c175e7a2c765d575d500948d34e05d44647aa8309cdebe49484c2dc`
- Source handoff SHA-256: `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e`
- Proof handoff SHA-256: `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415`
- R119 Lean SHA-256: `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`
- R118 Lean SHA-256: `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`
- Baseline receiver SHA-256: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`
- R117 patch SHA-256: `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`
- Receiver after R117 SHA-256: `542deb29c1143fad9adca958c3fadfa976e4505acc6f91dcf119ff0628f07e31` (296297 bytes, 5864 lines)
- R119 patch SHA-256: `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a`
- Final virtual receiver SHA-256: `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` (296776 bytes, 5875 lines)

All twelve full old-context payloads had one ordered, nonoverlapping match; hunk counts and actual coordinates matched. The source handoff correctly discloses that R117 hunk 6 relocates from advertised old line 5106 to actual line 5109. The evidence supports this unique-context composition, not strict advertised-offset application.

## Source and proof findings

In the composed receiver, capture searches `permission.concrete` and stores both the optional member index and the permission reference. Request construction copies both fields directly. The consumer checks unique registration, the captured packed index and `std::ptr::eq`, then calls `.get(index)` on `self.catch.permission.concrete`. Baseline effect lookup constructs the retained slice from `&permission.concrete`. The starting-address check does not establish slice length or arbitrary provenance; the handoff does not overclaim this.

For `[4,9,9]`, first search returns index 1, but changing the index to 2 still passes the local family read. Thus the guard alone cannot authenticate first-index transport. Empty/missing values, out-of-range and `None`, duplicate registration, foreign owner/state/batch and different record address are bounded as guard observations, not executed/reachable counterexamples. Registration, packed slot, native member, concrete index and family remain distinct.

The proof handoff identifies the first missing premise: no existing authorized relation derives `orderedSearch permission.concrete providerFamily = some permissionMember` from the actual Rust vector, equality and `.position()`. R119 assumes this equation; R118 does not model the new index transport. Later reference transport and indexed-read interpretation also lack formal bridges. Another finite membership lemma would not close this correspondence.

## Preserved gates and review method

R119 declarations remain unchecked; no theorem-type or full axiom output was observed. R39 PRE-state registration absence, R45 extraction identity, R114 transport, full source soundness/effect hygiene and production remain open. Promotion needs an authorized interpretation for this exact source computation and field transport, plus required Rust/Lean verification.

The reviewer read raw patches, immutable receiver capture code, R119 declarations, governing authority and relevant tests (without executing tests), then read the handoffs. Review was read-only: no writes by the reviewer, source execution, build/test/checker, environment/storage probe, scratch/cache/worktree or Git mutation. No review-file hash exists from the reviewer; this primary-recorded report is hashed in the sprint outcome/checkpoint.
