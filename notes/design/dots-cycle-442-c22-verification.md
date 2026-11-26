# C442 exact focused verification

科学 pin `ca663ec06b47c9acdbfce2ad4e449e4284956551`; Lean tree `54677fdcb38877f141f5065ea342fd362471afdd`。開始時の authoritative `integration/m1-final@fbbf227b2023e0da5d18d8f5c3826545f6b79e28` (Lean `f9471c73c28ed615317a4de8ff847af8b093e97d`) が直前 C441 を採用していることを確認し、その旧 source closure を使用。

## Git と実行

- 6 個の production と 7 個の独立 Audit の **実 Git bytes** を科学 pin から取り直して 13 blob SHA-1 を照合。旧 production 7688 と旧 Audit 2076 の全ファイル IDs、その他 Lean 項目は同一。barrel は旧 376321 bytes を完全な prefix として 6 import を append のみ。凍結 `Audit.lean` / `README.md` は blob IDs のみ比較。
- official Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）。独立検証が actual 13 Git-fetched bytes から 6 production を topo 順に `lean --trust=0 -DwarningAsError=true -o <production-olean> <exact-source>` 個別に実行。各 Audit を空の別 cwd と production-only `LEAN_PATH`（Audit oleans なし）で `lean --trust=0 -DwarningAsError=true <exact-audit>` として実行: 全 exit 0。使った既存 focused source provenance 4,088 / 4,088 は正本の immutable bytes と一致。
- 担当側でも production-only exact imports を使い、以下 7 Git-fetched Audit の全ファイルを個別に `lean --trust=0 -DwarningAsError=true --stdin` で再検証して全 exit 0。#print 39 行は標準の `propext`, `Classical.choice`, `Quot.sound` のみ（またはその部分集合）。警告・カスタム公理・`sorryAx` なし。
- Audit の import: `Yulang.*` 以外 0 件。各 Audit 独立。全体 `lake build` / `tools/verify-lean.sh` / Rust は実行していない。
- [独立に実行した exact fixture の追試](dots-cycle-442-c22-qa-fixture.md) は同様の production-only 物理 source 1 本 exit 0、20 行標準のみ（うち公開 Audit と重複 6、追加 14）。公開 39 行には加算しない。

| exact Git file | blob |
| --- | --- |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedSource442.lean` | `c16e4bff6174e8256f43344a632958e1e5944fe4` |
| `lean/Audit/Cycle442I74MixedFixedSource.lean` | `09cdfc8c53518829f1a6b4a698b17ffcd51e6e59` |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedRead442.lean` | `af69c4a4d0b0a4c2795573d8a4e2b7e14b12f0d1` |
| `lean/Audit/Cycle442I74MixedFixedRead.lean` | `9eeb1d9be8dc0127b753327e942a62a004cc2d09` |
| `lean/Audit/Cycle442I74MixedFixedEndToEnd.lean` | `0b73359dbb2211b189aee2c373d376502d4c7447` |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedBoundary442.lean` | `cc29af042d5d6192296cd8b5b885ddcb9f2ac468` |
| `lean/Audit/Cycle442I74MixedFixedBoundary.lean` | `db25bb0ecd1ca86894957a9543bcc35d572701f0` |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedTypedRead442.lean` | `88b6e04fe46a1d3a862ccceb2cf0f027a3eb1ba6` |
| `lean/Audit/Cycle442I74MixedFixedTypedRead.lean` | `bd937732c81c5a3958d54da56e38a37f2816e3db` |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedCompanion442.lean` | `7df49d2a214ba91e230b5cd694817cf1e6f0d680` |
| `lean/Audit/Cycle442I74MixedFixedCompanion.lean` | `42f19a20cc1fff5351f2aabf529059ba68735600` |
| `lean/Yulang/GeneralDeclarativeI65I74MixedFixedDictionary442.lean` | `b460db08b3c5183864a2f7c0b941a9e5f737c973` |
| `lean/Audit/Cycle442I74MixedFixedDictionary.lean` | `78047707a032fc2037773c0e02dddc8693844991` |

## 七本の標準 axiom 出力（exit 0）

### `Cycle442I74MixedFixedSource.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.ref_tree_instantiates_exact_slots442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.actual_ref_value_reads_own_typed_centers442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.ref_tree_has_no_legacy_code442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_output_keeps_occurrence_and_order442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_output_receipt_reads_a_mixed_rhs442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_output_fixed_iff_same_target_equals_mixed_value442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_output_has_no_value_only_fixed_code442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedRead.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.inputOnly_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.inputOnly_original_K2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.originalTapedChoice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.restored_input_is_exact442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.read_named_output_keeps_original_address_and_body442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.replay_uses_exact_selected_original_input442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedEndToEnd.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.original_mixed_associated_source_replays442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.replayed_exact_original_fields442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.every_input_and_target_row_fits442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.actual_replay_has_signed_mixed_value_at_original_target442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.same_ref_type_requires_same_row442' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example.original_fixed_targets_can_fail_after_real_source_replay442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedBoundary.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.legacy_fixed_value_emission_iff_original_typed_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.any_original_row_need_excludes_legacy_fixed_value_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.any_event_row_need_excludes_old_retained_row_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.old_expr_reads_only_value_projection442' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.independently_varying_original_effect_excludes_any_old_denotation442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.old_alias_target_relays_only_independent_mixed_equality442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedTypedRead.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.readRefPlan442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.replayedOriginalRef442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_ref_encoded_output_nonflattened442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_named_output_unique442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_replayed_ref_equates_same_event_output442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.original_replayed_ref_is_the_fixed_target_slice442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.exact_ref_output_uses_original_head_centers442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedCompanion.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.two_kind_ref_equivalent_iff442' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.existing_mixed_descriptor_point_exact442' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.existing_companion_has_independent_typed_fixed_equality442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.existing_companion_and_original_Fits_are_separate442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `Cycle442I74MixedFixedDictionary.lean`
```text
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.actual_replay_frame_keeps_its_own_head442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.actual_mixed_replay_with_retention_is_original_dictionary442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.MixedFixed442.actual_mixed_replay_with_existing_typed_companion_is_dictionary442' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
