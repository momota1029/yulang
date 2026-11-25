# C423 C14: 固定先を保持した projected B6 RHS

技術ピン `0e874ffa3375f1e87d898b1827a0f4e293eb667f`、Lean tree `676be2d5bcb2f5d964101d24823f089f0ab181a3`。元の `SourceHead`・`HeadMeaning`・`DictionaryEvidence`・公開 R13 checker は不変。これは分類成功ではなく、C14 の**固定先保持と値側**の証拠。

- `original_projected_B6_write_is_retained_at_its_exact_target423` は、同じ State の同じモデルで、元の B6 から出現・宣言/出力 ordinal・固定先付きの実 required value を得て、その固定先がその値と同値であることを証明。両端の field 3,4 はその値と非同値でもよく、別の実補助制約から用いる。中心の literal 行は不要。
- `original_projected_B6_fixed_target_survives_distinct_logical_names423` は異なる補助 field 7/10 と結果式が読む 11 に二方向の実制約を使う。各方向がないと、同じ B6 RHS に対して固定先は別の型を持つ具体的適合モデルがある。`checked_path_retains_the_exact_original_B6_value423` は元の raw 間隔行／ordinary `tyLe(var,var)` を四本の有限の列として検査。実例は直辺なし。
- `original_B6_projected_write_retained_even_without_optional_agreement423` は元の中心を二つの別の ordinary 型制約で挟み、同じ B6 required projection だけを固定先へ結ぶ。実モデルで required/optional は非同値のまま。旧の literal 再構築で代用していない。
- `read_retained_Pick_write_sound423` は具体四経路を同じ source/B6/target reader にまとめた。証人は行の座標と向きだけで verdict や型値を指定しない。二つの異なる実保持行 (4,11)/(5,7) も、同じモデルで原出現・元 ordinal・target と値が一致する。
- 実例で旧 R13 入口も試験した。同じ実 retained target が成立しても、現行 head が欠けるため選択報告は任意の旧証人で通らない。新しい言語上の拒否ではない。C14 は未完、残り 9 行。

## 20 分時点の再生

Git の exact bytes、凍結 2 blob ID、元 barrel 全文への追加 import を照合。Lean 4.35.0、`lake env lean --trust=0 -DwarningAsError=true`。C423差分と C422–423 結合差分の独立再生は PASS。C409–423 の最広スコープと旧 55 対照はこの公開時点では続行中。実装の新規公理、sorry、全体ビルド、Rust 実行、停止性や NoFalseRejection は主張しない。

## I-75 live order, read at 18:56 UTC

Integration `b2fe5a3d9324aa1ef2964c95f7445884ee4dd66e`, Inbox blob `42ed184178357af37ba86de355218d720cb36746`. I-75 authorizes corresponding additive source and semantic constructors, keeping the existing literal branch and outer statements. All existing evidence including C422’s legacy inversion and C423’s old-entry test concerns the pre-I-75 head. The retained projection work published before I-75 remains valid on its exact pin. C14 is still open; no new checker is deployed in this checkpoint.

## Final published Lean tree verification

The final audited code at `7e882f6e1ca10e57dbc9a120941a5e1f82621ed9`, Lean tree `6c9271038132d871565a7f85fbda7bcfcb33b233`, was replayed in exact-byte independent C423-only, C422+C423, and C409–C423 retained scoped contexts. Lean 4.35.0 `--trust=0 -DwarningAsError=true`; appended exact imports and standalone audits passed. Only standard reported axioms (`propext`, `Classical.choice`, `Quot.sound`). The 42 prior positive/negative cases and 13 public R13 combinations replayed successfully on the unchanged prior entry; not regression through an R14 that does not exist. Full repository builds and Rust were not run. Frozen files were checked by Git object ID only.

The effective candidate includes the 18 changed Lean paths (9 sources, 8 standalone audits including semantic fixture checks, import barrel with complete old bytes plus 9 imports). The isolated Heads367 constructor test and speculative new public receipt representation are **not part of the published Lean tree**. This distinction holds even when individual scratch tests pass.
