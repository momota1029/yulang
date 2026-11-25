# C422 C14: 実例・証拠の境界・検証方法

- 技術ピン `2d74668d6979bcad61851c422db0a858a6aed57e`、Lean tree `eeb7776992d0875822bcb8291c583583b1acfb90`。変更は C422 の新規 Lean 9 ファイル・独立 audit 7、既存 barrel は import 追記のみ。固定 `SourceHead`・`Event`・`DictionaryEvidence`、公開 `RepeatedCenters421.check` と `check_sound` のいずれも変更なし。
- [設計と次の証拠表現](dots-cycle-422-record-endpoints.md)・[I-74 の適用範囲](dots-cycle-422-c-coverage.md)。[仕様 §6.3](https://github.com/momota1029/yulang/blob/2c89fd40a05965ea8438cd8c169ecf7e2e096a6f/spec/06-roles.md#L395-L408) の `Pick` 自身を表す。外側の W/Hold の solver 展開を再現したものではない。

## 確かめたこと

1. `readEndpoints422` は元の要求から引数の三つ組 `(0,1,2)`、原宣言・関連型の本体・原結果先、上下端点独立の由来と record 行を取り戻す。中心 1 に record 行がなくても読みは成功。これを既存の成功 `Classifies` と同一視しない。
2. `same_model_endpoints_support_both_projected_channels422` は任意の適合割当てで、元の実中心に対する二つの field 射影をそれぞれ挟み、残りを同じ実中心の mask で挟む。元の lower/upper field 名は 3/4、residual 名は 5/6。中心をどちらかの端点と同一視しない。mask は一般の exact delete と同一ではない。
3. `primitives_only_cannot_add_genuine_nonpoint_record_selection422` の前提は、実際の C14 端点読み、中心 record 行なし、端点が異なる適合モデル。結論は任意の規則集合 `R` と任意の辞書 `d` に対する選択の不成立。全 `SourceHead` から逆向きに示した。ただし、意味上同じ field/tail operands の点対照なら、root 名が違って中心行がない場合も旧証拠を作れる。
4. `fresh_record_model_extension_exactly_when_channels_agree422` は別 ordinary State への fresh literal 行の保守的延長と、元の fit と required/optional の一致の同値。元の列・結果先を保護する。原例の二つのモデルではその延長に成功するが、同じ要求の第三の適合モデルが両 channel 一致を反証する。新しい名前だけでは全モデルに対する元の証拠を作れない。`ProjectedRecordChannels` はこの第三のモデルでも成立する。
5. `fresh_projection_names_exist_without_required_optional_agreement422`: ordinary State に **行を足さずに**、どの fit でも別の割当ての未使用座標に required field と実 mask を設定できる。元の制約・座標・結果先は保つ。具体的第三モデルでは `Fits` も全て保持し、required/optional は依然異なる。`same_split_source_admits_fresh_projections_without_a_literal_row422`。同じ元モデルの任意の未使用座標を正しいと仮定せず、旧 `SourceHead` の証拠には転用しない。
6. `original_B6_binder_yields_required_projection_and_exact_addresses422` は、実ソース lookup と B6 atlas の型つき木をそのまま使い、元のモデルで projected binder を評価。実例の `([61,422], decl=1, out=0, target=12)` を保ったまま、同じ入力の三つの fit によって値側は `int`、`int | bool`、`top` と変わる。これは `RHS` の値だけで、固定先の等式・台帳・辞書が実際に保持されたという報告ではない。
7. `split_channel_model_rules_out_literal_ordinary_HeadMeaning422` は構成子の不足より強い。第三の適合モデルではどの記号捕捉を選んでも、旧 `HeadMeaning` が要求する「実中心 = literal record」が成り立たない。新しい構成子から旧と同じ literal 意味を返すだけの修正は健全ではない。
8. 既存入口の不受理は旧形式がその選択証明を持てないこと。型エラーや保留を根拠づけていない。`actual_spec_pick_source_cannot_be_added_by_primitive_union422` と `unchanged_public_entry_cannot_emit_selected_fixture422` を参照。元の B6 binder があり実中心から field の区間を読めても、固定結果先への出力保持は別の証明であり、旧 State では導出していない。

## 独立再生

Git から exact pin の bytes を別に取得し、`git hash-object` で SHA を照合。古い full barrel が正確な接頭辞で、追加分は九つのモジュール import のみ。凍結 `lean/Audit.lean` と `lean/README.md` の内容は読まず、blob ID のみ照合。

Lean 4.35.0 / commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。各 `.lean` を `lake env lean --trust=0 -DwarningAsError=true <path>`、source は `-o <output>` 付きで再生。suffix で旧依存 `GeneralDeclarativeRecordMask330`・`GeneralDeclarativeRecordReconstruct330`・`GeneralDeclarativeRecordNames330` を元の Git bytes で再生しただけで、リポジトリでの変更ではない。唯一の監査差分は各新規 audit。

| 再生対象 | source（旧補助依存 3 を含む） | audit（異なるファイル） | 公理出力の定理数（異なる名前） |
| --- | ---: | ---: | ---: |
| C421 までの依存 + C422 差分 | 12 | 7 | 36 |
| C420 までの依存 + C421–422 | 22 | 14 | 70 |
| C408 までの依存 + C409–422 | 130 | 71 | 600 |

source・standalone audit・追記 import の再生はいずれも exit 0。公理出力は `propext`・`Classical.choice`・`Quot.sound` のみ。C422 の差分は 36 種。新しい公理・`sorry`・`native_decide` なし。

- 以前の 42 + 13 対照を、変更していない R13 公開入口で再生し一致。C422 audit は、不足する根拠・すり替えた行・異なる実中心モデル・実 B6 binder・相対延長可否・任意の旧入口証人を分離している。
- 追加 scratch harness（Lean tree には追加せず）で、元要求の low/high origin・low/high 行・decl ordinal 各 0–3（20 件）の対照が期待値どおり。low 0/0、high 1/1、decl 1 のみ正しい。独立の closed ordinary record 行 2 が `0 → 3`、alias 行 3 が `3 = 0` となる raw 根 K2 の試験は、新しい端点リーダーでは成功せず、旧の実 rawRoot 入口は拒否報告を受け取る。open 行の非対応から循環の不存在を推論していない。反対に、同じ decoded root から到達する field だけに自己環があっても、この二つの変数で受ける head は field 内部を調べないため、新しい端点リーダーは成立し、元の根 K2 証人は不成立。
- 同じ scratch は、原要求に対し実 B6 binder が存在しても、実中心から射影された `int | bool` が元の固定結果先 12 の型としては導けない適合割当てを確認。これは fixture の未保持出力であって、言語の拒否規則ではない。

- 追加の独立 scratch（配布 Lean の外）で、atlas の元の occurrence、宣言、出力 ordinal、または宣言本体 ID のどれかが違えば、端点読取りが成功しても B6 RHS は読み出さないことを確認。同じ出力要求の target を 12 から 13 に変更した対照では値側のラベルも正確に 13 を運び、locator で別の結果先を選ばない。
- 別の scratch で、両方の元制約を保持する相対割当てで新しい射影名を読む旧 tree evaluator と、元のモデルでの直接射影評価の値一致を確認。`DictionaryEvidence` 自身が同じ `Event.head` を含むため、元の非点例の適合モデルで旧辞書証拠も任意の辞書について成立しない。分類の名前を付け替えるだけでは修正にならない。
- 原要求で中心行を追加せず、固定先 12 に `12 = 7` を保持して実 RHS `int | bool` と同じ型を持つ具体モデルでも、いずれの規則集合からも旧選択は作れないことを別 scratch で確認。これは 1 モデルでの対照であり、一般の固定先保持を証明したとはしない。頭証拠の不可能性を「単に結果行がなかった」ことと区別できる。

- 同じ authored source の二つの適合モデルで実中心型が意味上同値なら、元の B6 RHS の値と mask residual も意味上同値。端点名の一致を根拠にした同一視ではない。この transport も独立 scratch で strict に確認。

結論: C14 の三条件のうち R14 選択局所規則・入口拡張・追加源での固定健全性は未完。C15 には進まない。Rust・全体ビルド・全仕様の完全性・停止性・NoFalseRejection は未検証。
