# C437: 公開 Git bytes の scoped Audit 再検証ログ

- 対象 C437 技術 pin: `ed7e39f81d521b556dd37962b3b4baa5cb9b2351`、Lean tree `07eaa114f990a25365054ea6bd17ddc2b4ad46c2`。
- Lean: version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release。
- 各 Audit の公開 pin から raw source を取得、個別に標準入力へ。production olean だけの `LEAN_PATH` で別プロセスに `lean --stdin --trust=0 -DwarningAsError=true`。以下はその出力全文。各 Audit は別途、個別の production build に対する standalone file としてもチェックした。
- 全体 `tools/verify-lean.sh`、full Lake、Rust は未実行。チェックの結果を R18/public checker の実行結果とは数えない。
- Audit の import: `Yulang.*` 以外 0 件。

## `Cycle437I74CompletedLowerCenterReader.lean`
blob: `a4f99a7035c8d27c2e8c112ff970f1d7a9aa91ce`、exit: 0

```text
'Yulang.GeneralDeclarativeI65.I72.CompletedConsumer437.readCenterAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedConsumer437.exact_empty_invocation_reads_original_capture437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437ReadCompletedCenter.exact_center_reader_checks_original_issuer_after_election437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437ReadCompletedCenter.read_scoped_consumer_same_model437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `Cycle437I74CompletedLowerConsumer.lean`
blob: `a834fcec9376335dc542b6419560890efcc0b1aa`、exit: 0

```text
'Yulang.C437CompletedConsumer.lower_has_no_original_source_route437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.consumer_source_receipt_and_original_upper_stay_distinct437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.original_center_keeps_three_distinct_payload_names437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.original_occurrence_selects_only_in_the_current_scoped_rule437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.selected_producer_lower_and_consumer_in_same_fitting_model437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.consumer_can_use_the_lower_without_an_authored_lower_in_a_real_model437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437CompletedConsumer.raw_alias_change_k2_control437' depends on axioms: [propext, Quot.sound]
'Yulang.C437CompletedConsumer.changed_raw_graph_has_actual_root_k2_437' depends on axioms: [propext, Quot.sound]
```

## `Cycle437I74CompletedLowerExactFixture.lean`
blob: `de7069a9afac496e8327b0e2a4e0631f194c80a0`、exit: 0

```text
'Yulang.C437RetainedFixture.atlas_guards_original_occurrence_and_declaration437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437RetainedFixture.retained_and_decoy_have_equal_values_in_fitting_sample437' depends on axioms: [propext,
 Quot.sound]
'Yulang.C437RetainedFixture.same_target_literal_decoy_is_not_the_typed_output437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437RetainedFixture.original_lower_meaning_ignores_unused_nativeSyntax437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `Cycle437I74CompletedLowerNativeHeader.lean`
blob: `29df5511b06b2d95b04711860a84390032a21928`、exit: 0

```text
'Yulang.GeneralDeclarativeI65.CompletedNativeHeader437.checkedDecl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.CompletedNativeHeader437.checkedHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437NativeFixture.Tests.source_body_replays_covariant437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437NativeFixture.Tests.genuine_native_header_not_legacy437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437NativeFixture.Tests.invariant_flag_cannot_stand_in_for_declaration437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437NativeFixture.Tests.duplicate_declaration_does_not_pass437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `Cycle437I74CompletedLowerRetained.lean`
blob: `21d5951b09bbc070aaeedf5a592a0d2c952f0662`、exit: 0

```text
'Yulang.GeneralDeclarativeI65.CompletedLower437.Payload.Means' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.CompletedLower437.retained_literal_typed_output_means_same_lower437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.CompletedLower437.lower_retention_uses_original_B6_value437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `Cycle437I74CompletedLowerSeedReader.lean`
blob: `9f8854068b4968120c000d8da3ae53e29a7203e1`、exit: 0

```text
'Yulang.GeneralDeclarativeI65.I72.CompletedSeed437.checked_row_has_exact_ordinal437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedSeed437.chosenTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.CompletedSeed437.readOneOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437ReadSeedOutput.seed_reader_uses_actual_original_source_and_row437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437ReadSeedOutput.replayed_seed_and_output_hold_in_all_fitting_models437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `Cycle437I74CompletedLowerSelectedSeed.lean`
blob: `b80b1f583886c7d3f9c47341378499a0d0b7bd0a`、exit: 0

```text
'Yulang.C437SelectedSeed.selected_seed_and_its_lower_in_every_same_model437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437SelectedSeed.seed_and_retained_value_when_lower_has_no_authored_syntax437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437SelectedSeed.source_root_is_safe437' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.C437SelectedSeed.elected_frame_is_the_actual_typed_frame437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437SelectedSeed.one_selected_source_supplies_exact_retained_lower437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.C437SelectedSeed.selected_seed_has_dictionary_in_every_fitting_model437' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Production の公開 bytes の再読み

上記同じ strict stdin 設定で 5 本をそれぞれ再実行。全 exit 0、stdout/stderr 空。

- `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerCenter437.lean`、blob `a41f1c9ef4d5b9ccc3a21f80b5d13c60cbfe611a`、exit 0
- `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerNativeHeader437.lean`、blob `bd33069284de0bede70e0e159cc491b543013529`、exit 0
- `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerPayload437.lean`、blob `12c970f8dab79c7a089ded26b5771f4040b356e1`、exit 0
- `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerRetained437.lean`、blob `89578ca0282859455cf83341589c71ee5d07005e`、exit 0
- `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerSeed437.lean`、blob `1031f22ea6a046b6a2d2ae04e31210a37c0d2a8a`、exit 0

追記点の Git subtree も比較した。旧 `lean/Yulang/` の 7,660 entries、旧 `lean/Audit/` の 2,043 entries は名前・mode・blob ID が全て不変。総 import の既存 bytes の削除なし。frozen は内容を読まず blob metadata の不変のみ確認。
