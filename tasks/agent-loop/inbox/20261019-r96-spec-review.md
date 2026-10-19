# R96 independent pre-edit specification review

Reviewer: fresh `spec_auditor`, independent and read-only. Primary-preserved report transcript.

**CLEAN — R96 pre-edit specification review. No blocking/major/minor findings.**

- Controlled pair: contract lines 8–23 fixes every source component except `catch pending` → `catch thunk`. Both formal declarations and `helper(thunk)` remain identical. Compare final expanded source strings during delta review; source-branded IDs need not be numerically identical across separate inputs.
- Expectations are explicitly falsifiable candidate observations, not approved semantics (contract lines 21–27). Existing expectations remain protected by `rules/testing.md#expected-output-protection`; no existing assertion or semantic test name is authorized for alteration.
- Candidate mechanism supports investigating the contrast: `program.rs:414–432,488–505` selects computation roles/schema; `machine.rs:879–895,977–1005` creates inherited argument views and receiver entries; `machine.rs:1478–1490,1860–1884` preserves direct-formal views and execution receipts. `receiving.rs:230–323` requires the candidate owner's boundary in an authenticated observed image; `machine.rs:1580–1592` returns HandlerEvidence when no positive local grant exists. This supports the hypothesis without proving inference success or either complete outcome.
- Governing source behavior remains charter §21 (`notes/design/2026-09-29-scc-intrusion-redesign-charter.md:572–601`) and whole-argument construction (`notes/design/2026-10-02-source-call-scheduling-choice.md:13–58`). R88 §2 limits its bridge to U/O/S; its facts cannot directly certify this nested-helper source.
- Contract lines 27, 42, 48 retain native/proof/user gates and require stopping on surprising evidence. Lines 38–42 authorize one exact filtered command, executed by Luna after source freeze and CLEAN delta review, covering both examples.

Verified SHA-256 values:

```text
contract          195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892
runtime_receiving 355c3cfb6b505780b0eeaf93e6f5b2b443182b2be20912824383b4a6b8bfd357
receiving         8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
program           484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11
machine           fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
R88 bridge        185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782
```

Read-only review; no files changed, Git used, builds/tests/CLI run, or descendants spawned. Final test/source/proof diff remains subject to required delta review.

## Post-freeze delta confirmation

Reviewer: same independent `spec_auditor`, read-only; primary-preserved report transcript.

**CLEAN — R96 post-freeze spec delta.**

- Frozen test SHA verified: `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2`.
- Frozen proof SHA verified: `2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9`.
- Removing only the added test restores exact baseline SHA `355c3cfb6b505780b0eeaf93e6f5b2b443182b2be20912824383b4a6b8bfd357`. Existing tests, assertions and names are byte unchanged.
- `runtime_receiving.rs:158–168` contains the contract's exact positive source. `replacen("catch pending", "catch thunk", 1)` produces the controlled negative; no additional source difference.
- Proof sections “Parent and application,” “Candidate preparation seam,” and “Conditional finite runtime derivation” preserve candidate status, explicitly leave public preparation/outcomes unobserved, and deny semantic adoption or parent closure. R88 reuse is confined to applicable grammar fragments.
- Contract lines 38–42 authorize one command filtering `nested_helper_permission_tracks_its_own_received_view`; that single test invokes both assertions. Any preparation failure, unexpected outcome or blocking/major review stops R96 without repair/retry.
- Authority: R96 contract lines 8–27, 34–48; `rules/testing.md#expected-output-protection`; `rules/design-authority.md#approval-and-implementation-gate`. No old expectation was changed and no new semantic decision requires adoption in this candidate evidence slice.

No findings. No files changed, tests/builds/compiler CLI/Git run, or descendants spawned by reviewer.
