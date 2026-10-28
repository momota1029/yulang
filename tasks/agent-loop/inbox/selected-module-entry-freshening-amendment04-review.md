# Independent review — amendment 04

Disposition: **PASS for the authenticated three-owner research candidate.** No BLOCKING, major, or minor compiler-correctness finding remains in the reviewed delta.

Reviewer: `/root/selected_module_fresh_review04`, fresh nonauthor read-only reviewer. Assignment: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`, amendment 04. Charge the full 300-second grant; actual elapsed was not independently measured. Reviewer state: **STOPPED**.

This review grants neither baseline admission nor verification authority.

## Authentication

Isolated worktree: `isolated/selected-module-entry-freshening-repair-r1`.

Authenticated committed baseline: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.

All three owner pins matched before their source bodies were read and again at final source recheck:

| Owner | SHA-256 |
|---|---|
| `candidate_effect.rs` | `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6` |
| `candidate_scheme.rs` | `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e` |
| `shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |

Authenticated governing contracts and receipts:

| Input | SHA-256 |
|---|---|
| Base contract | `1091467e92e7231bc416190eb9c0727d39fadfdcafcbc78a2c1dcd4b26e40fb2` |
| Amendment 01 | `0e4c6e266723fc7795f9481fbea4f8466f1237e0a7eefefe8b466adec71310be` |
| Amendment 02 | `0a5f04b2b68a714eb16ef6c3e5668a075b684f29de537262f7c50057c463bfd9` |
| Amendment 03 | `6c155dd154d1cd106ad41b2484f870570e63d61f0b0ff2cf2f4643ffd27261e9` |
| Amendment 04 | `3711cca5dc9cbaa6eb94cb3589d4c10ff0844a5a4639168bec82106b06fe3bc1` |
| Original rejected baseline review | `ed3dc72a7c1ab1301294a5e9822f2251273d1656d775ae5db726ff08b09ec3c9` |
| Prior amendment-02 assignment review, stored as `selected-module-entry-freshening-amendment01-review.md` | `676b54b6848a33219a3dff09749c682805d6f3cf3722f4eff0d347adb5771e30` |
| Frozen isolated repair handoff | `e42935e4490887b0b7604fa8fb188afd28c6272c733a38dea8a87e4cb2e55df3` |
| Frozen prefix-repair handoff | `c33b3a08961898a81662c5b9e6a5e1fce32a57206e8c1e9b95f2e0bee20421fa` |

Amendments 02/03 resolve the worktree locator and erroneous shadow-apply transcription. The final owner bytes match the corrected pins.

## Independent source conclusions

The repairs address the identified causes at their owners:

- **Protected regression restored:** `candidate_effect.rs:3199` retains `tuple_formal_permissions_keep_element_paths_and_transaction_ownership`, including the original nonrecursive `my f(...) = pair`, consumer assertion, publication assertion, and transaction checks. Its complete test block equals the committed baseline verbatim; SHA-256 `a48b72d711394956321587ed7d51e33bb01f09899827e3d0a2421baaded6f8cf`.
- **Publication producer repaired:** `candidate_scheme.rs:2865` emits `negative-root-publish term={term:?} node={index} ...`. Capture identity follows those protected fields. The unchanged assertion at `candidate_effect.rs:3236` can therefore match the producer’s prefix.
- **Recursive probe separated:** `candidate_effect.rs:3272` independently names `formal_permission_recursive_transport_probe`. It does not replace the original nonrecursive regression.
- **Missing constructor identity handled structurally:** memo hit/miss events at `candidate_effect.rs:1531` and `:1554` require `Some(constructor)` without inventing an identity. The shared helper remains reachable from formal-entry (`:1812`), signature annotation (`:2497`), and computation annotation (`:2279`) paths without that precondition. Text events tolerate `None`. The new regression at `:3277` exercises formal-entry, local, and root-computation routes with tracing enabled.
- **State ownership:** constructor tracing uses a drop guard; delegated-site tracing restores its previous context through its own drop guard. These observer changes do not alter solver memo results, constraint insertion, or return values.
- **Capture/export consistency:** instrumentation records the original row before canonicalization, the canonical endpoint and interned node, the actual materialized row node, and the published graph owner. Export tracing observes the checked returned permission port. The complete `shadow_apply.rs` delta adds only that test-gated event and the two required test-literal fields.
- **Graph literals:** the capture literal at `candidate_scheme.rs:2644` initializes the test-gated capture identity. Both explicit scheme-Graph test literals at `shadow_apply.rs:4956` and `:5070` initialize it to `None`. The isolated source search found no additional literal of this scheme Graph requiring that field.
- **Phase/feature boundary:** the modules belong to `shadow-apply-candidate`; added observer state, graph fields, instrumentation, and test helpers are gated by `cfg(test)`. The remaining non-test edits are formatting or an equivalent local binding around the unchanged signature-effect call. No changed non-test solver behavior was found.

The review inspected source before reading implementer handoff explanations. Those explanations did not establish these conclusions.

## Complete delta

Against the exact committed baseline:

| Owner | Net diff | Diff SHA-256 |
|---|---:|---|
| `candidate_effect.rs` | `+794/-10` | `1f937820021c6a771a480fe7ac2fbc868228efb715c5a09ef8e73c19130e4036` |
| `candidate_scheme.rs` | `+62/-4` | `515c7d81e5de72634b4b38a3ce434804f043607b68efd55afac487286d56b024` |
| `shadow_apply.rs` | `+7/-0` | `41b7b64ab37dd04f8b2eb9c1915e5ebad48b4f70f17545e429d07427b52ab6ff` |

Combined three-owner diff SHA-256: `df60549fef05cc1800eba37aabb998470d1d8a0d700edbf4325e234638fd916b`.

## Limits and deviations

No files were written. No descendants, builds, tests, Cargo, Lean, Git mutations, shared dirty source reads, runtime-owner reads, or quarantined-path inspection occurred. Static reads, read-only Git comparisons, and hashing were used. The first static hashing helper attempted unavailable `python`; `python3` completed it without writes.

Compilation and test outcomes remain **UNVERIFIED**. The unresolved unequal-transport probe is preserved; this review does not certify its assertion. Any later verification must follow amendment 04’s exact-test and resource restrictions.

The inspected authority retains the complete original source root, dependent fields, scopes, and shared witnesses. Instrumentation and bounded observations do not establish their whole-language correspondence. Source/native reconstruction, original whole-branch allocation-root correspondence, H_u, A/B, effect-hygiene, and production gates remain OPEN or AUTHORITY_BLOCKED.
