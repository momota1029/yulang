# R32 independent review — Luna intake of terminal report

**Attribution:** This file is Luna's intake/record of the terminal independent review message from `/root/effect_permission_r31_review`. The reviewer role remained read-only and wrote no file. The reviewer reported no descendants and stopped. Observed model/effort UNKNOWN; aggregate review active time UNKNOWN.

**Disposition:** PASS for the covered finite-projection artifact gate. No blocking, major, or minor correctness finding. This does not complete primary synchronization or closeout by itself.

## Coverage repair and application

The reviewer checked `NativeCallbackGrantBridgeR32.lean:767–951`.

- `coveringTable` constructs operation entries `[r,c,a]` and family entries `[r.family,c.family,a.family] ++ families`. The three referenced operations and every complete permission-row family are covered by construction.
- `referenced_operation_round_trip` consumes operation and family coverage. `covered_operation_keys_distinct` proves distinct referenced structural operations keep distinct keys.
- `covered_family_membership_iff` consumes complete row coverage and queried-family coverage. `permission_row_round_trip` recovers each row member.
- `covered_checked_catch` constructs its own covered table; callers cannot supply an arbitrary uncovered table.
- Decoder results at `:908–920` derive operation equalities consumed by `CatchReady` at `:943–944`. Covered family equivalence at `:921–925` supplies the permission-membership guard. The conclusion returns request, consumer and arm decode equations, family-membership equivalence, and checked-Catch.
- The remaining typed operation equalities are explicit premises. The theorem does not authenticate those equalities from execution; this is accurately stated as an open native-provenance obligation.

The R31 defect is repaired: an uncovered table cannot be supplied while bypassing the round-trip guarantees.

## Falsifiers and sibling cases

The old empty-table collapse remains explicit at `:852–857`, with `empty_table_not_covered` at `:860`. An empty table cannot instantiate the covered theorem, whose operation table is always `[r,c,a]`; an empty permission row cannot satisfy the required family-membership premise.

Duplicate identities preserve first-index member round-trips. The complete row retains unrelated families. A query operation's family being in the table alone cannot grant permission when that family is absent from the permission row; covered membership equivalence prevents it. No identity collision, failed round-trip, omitted family, or spelling/Debug identity weakening was found.

## Rust source-owner evidence

The reviewer independently checked the streamed pinned archive against the Rust mapping handoff:

- `machine.rs:2661–2667` admits the selected Catch operation only after typed equality with the pending request operation.
- `:2753–2784` records selected operation, typed arm key, consumer operation, and the index joining consumer to selected installation.
- `:4276–4293` validates shared event, installation, owner, operation, and typed arm joins.
- `receiving.rs:70–101` retains the admitted closed callback-result family row; `:583` copies it to route evidence; `:703` checks equality with retained schema; `:741–742` checks expected typed family and membership.
- `machine.rs:4096–4114` resolves family/operation indices by typed equality within the supplied machine HIR; `:4125–4127` serializes every permission-row family.

This supports same-snapshot source ownership for the recovered candidate. Serializers fail via `expect` if an identity is absent. The selected arm's Debug serialization is lossy and does not authenticate its `SourceNodeKey`; its typed key remains internally available. HIR numeric indices and Lean local table indices are different coordinate systems. Translation into Lean records remains native extraction work.

## Independent Lean audit

All 41 declarations were checked with pinned Lean 4.35.0 on stdin under read-only bwrap. Three subprocess audits exited 0 with empty stderr and no Lean diagnostics. Printed types/premises were inspected; complete axiom blocks match the frozen receipt. A comparison helper initially failed because of differing universe printing settings; matching the settings resolved that receipt-comparison issue, not a Lean declaration failure.

New R32 theorem axiom groups:

| Theorems | Axioms |
|---|---|
| `referenced_operations_covered`, `permission_families_covered`, `entryWithRow_use_ready` | none |
| `referenced_families_covered`, `empty_table_collapse`, `empty_table_not_covered` | `propext` |
| `referenced_operation_round_trip`, `covered_operation_keys_distinct`, `covered_family_membership_iff`, `permission_row_round_trip`, `covered_checked_catch` | `propext`, `Quot.sound` |

Across all 41 declarations: nine use no axioms, nine use only `propext`, and 23 use `propext` plus `Quot.sound`. No `sorry`, `admit`, project axiom, `native_decide`, or kernel-check bypass occurs. Independent audit subprocess time: 2.392655932 + 2.513758287 + 2.291995713 = **7.198409932 seconds**. No build, cache, copy, extraction, log, scratch output, source edit, or Git mutation.

## Frozen artifacts and dependencies

All hashes match the frozen contract/manifest and producer receipts:

| Artifact | SHA-256 |
|---|---|
| R32 contract | `85f1bd3d6350be8c501b0859230389d288901cceb9aa4982e57784842dcb5817` |
| R32 manifest | `91495c9955c39ce6988421d1913803788c26aca3d8d8ea47c224d837dcb0ef66` |
| R32 Lean module | `bf2908ae347814c71ddc32ffae0f64a62103b855d96655a47aa1b9db0dc9690c` |
| R32 proof handoff | `be7b68b1682f709bad5c624ca57e27a806df63848f7eafe938710ca84438a0a0` |
| R32 Rust mapping | `288c5b448e4fd7e2531e52d6689037700cfd7c1aca6ae07c653c3129cbd1dcb7` |
| R31 review | `d8e095ba4e9731478549912079ac60023556a6f89801bbd6e36915a67e6bd7f5` |

Dependencies: exact 36,175-byte R31 prefix SHA `a0a8b53e1f73ed44e92ee01b3e87531d310775af0804999d30d6fbb0a68e378d`; exact 24,342-byte R26 prefix SHA `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`; R30 archive SHA `5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`; archived `machine.rs` SHA `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`; archived `receiving.rs` SHA `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.

## Open obligations

Native extraction must still establish faithful identity atoms and numeric conversions, source annotation/Name/Apply provenance, complete source row, request-owned observations, Grant and invocation-guard lookups, dynamic installation/arm extraction, and actual request emission from one authenticated snapshot. `entryWithRow` projects a supplied row; it does not authenticate the source annotation. `callbackSlice` constructs supplied-record state; it does not establish native store membership or emission. No native Step/History, arm-body result, whole-language hygiene, original A/B closure, soundness, principality, progress, termination, or production claim follows.

**Terminal receipt:** reviewer stopped; no file writes, descendants, generated outputs, or unresolved child leases. This intake records the independent review without attributing authorship to the reviewer.
