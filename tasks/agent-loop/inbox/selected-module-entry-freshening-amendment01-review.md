# Independent review — selected-module-entry-freshening repair

Disposition: **REJECT — repaired baseline cannot be admitted.**
Reviewer: `/root/selected_module_repair_review` (`compiler_referee`, fresh nonauthor).
Assignment session: `SELECTED-MODULE-ENTRY-FRESHENING-20261028/r1-amendment-02`.
Grant: 300 seconds charged in full; actual elapsed was not measured. Reviewer state STOPPED. No file writes, descendants, builds, tests, Cargo, Lean, Git mutations, shared dirty source reads, runtime-owner reads, or quarantined-path inspection occurred.

## Findings

1. **MAJOR — restored regression necessarily fails because its producer changed the protected trace format.** Isolated `candidate_effect.rs:3236–3237` requires a trace beginning `negative-root-publish term={domain_term} node=`. Isolated `candidate_scheme.rs:2865` now emits `negative-root-publish id={:?} term=...`. That is the sole publication emitter, so no recorded event can satisfy the assertion. The original regression was restored byte-for-byte, but its producer contract was not restored. This violates amendment 01's requirement to preserve the original regression and assertions, plus expected-output protection. Minimum closure: preserve the original prefix and append capture identity after the original fields; retain the protected assertion. Obtain fresh review and subsequently authorized focused verification.

2. **BLOCKING — amendment 02 pins different `shadow_apply.rs` bytes from the submission.** Amendment 02 line 12 and the launch message specify `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a9a78cf72ff`; actual bytes hash to `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`. The latter agrees with amendment 01, the base contract and repair handoff. This blocks complete authenticated three-owner review under amendment 02; it is an input authentication finding, not a source defect. The reviewer did not inspect this mismatched owner's body and does not claim its Graph literals were freshly reviewed.

## Independent source evidence

- The complete original `tuple_formal_permissions_keep_element_paths_and_transaction_ownership` block, including nonrecursive `= pair`, matches pinned base verbatim: block SHA-256 `a48b72d711394956321587ed7d51e33bb01f09899827e3d0a2421baaded6f8cf`.
- The recursive transport probe remains separately named at `candidate_effect.rs:3272`.
- Memo hit/miss typed events now require `Some(constructor)` at lines 1531 and 1554; missing identity is not fabricated. Formal-entry/local/root-computation routes share this helper, and a new traced regression covers those routes. This repairs the previously identified panic cause structurally; execution remains unverified.
- Inspected candidate-effect and candidate-scheme additions are `cfg(test)`; non-test solver operations remain unchanged apart from formatting. Feature ownership is `shadow-apply-candidate`, as established by isolated `lib.rs` and `Cargo.toml`.
- Exact authenticated complete diffs against base: candidate-effect `+794/-10`, diff SHA `1f937820021c6a771a480fe7ac2fbc868228efb715c5a09ef8e73c19130e4036`; candidate-scheme `+62/-4`, diff SHA `80f6650bb076da287cc85652ea0a3e745fadfd80eb21331c119cd5050b357370b2`.
- Reviewer inspected code before reading the implementer handoff. The handoff explanations were not used to establish source findings.
- The implementer's authenticated handoff records the initial prohibited read-only `git status` deviation. It does not establish a compiler finding.

## Authenticated inputs

| Input | SHA-256 |
|---|---|
| Base contract | `1091467e92e7231bc4166452a3dd34cfbcfd0d4b26e40fb2` |
| Amendment 01 | `0e4c6e266723fc7795f9481fbea4f8466f1237e0a7eefefe8b466adec71310be` |
| Amendment 02 | `0a5f04b2b68a714eb16ef6c3e5668a075b684f29de537262f7c50057c463bfd9` |
| Prior REJECT receipt | `ed3dc72a7c1ab1301294a5e9822f2251273d1656d775ae5db726ff08b09ec3c9` |
| Repair handoff | `e42935e4490887b0b7604fa8fb188afd28c6272c733a38dea8a87e4cb2e55df3` |
| candidate_effect.rs | `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6` |
| candidate_scheme.rs | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| shadow_apply.rs, actual | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |

Baseline: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. Amendment 03 corrects the shadow_apply pin; it does not change these source bytes or retroactively complete the reviewer’s three-owner inspection. Cargo admission is not authorized by this review. Source/native, H_u, A/B, effect-hygiene and production gates remain OPEN or AUTHORITY_BLOCKED.
