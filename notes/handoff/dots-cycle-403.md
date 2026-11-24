# dots-main 第403周（I-72 / I-65 Step 1）

**閉じた補題なし・分けた補題なし。** C380 の integration 残件は 14（未証明 3、部分証明 11）のまま。一般の `Classifies` と固定目標は未完成。C402 の暫定インターフェースに、この周で構成した具体的な規則を入れた場合の `DictionarySound` は Lean で証明した。

- 指示・基点: integration/m1-final `d030aff9cd025a75549c57c03245b32811b6310d` の inbox blob `2684940d16dd1b4f8aa76788a2719010b04a3bf4`、spec/06-roles と spec/10-inference-core、および work/dots-main の第402周 `16eaf8936901d40b8c74b235864d5b635a119a9a` を照合。I-72 に従い、S13 の文・固定の全称量化・言語の受理範囲は変えていない。
- **全可視候補・選択・捕捉:** [変数 head](../design/dots-cycle-403-i72-source-variable.md) と [繰り返す中心](../design/dots-cycle-403-i72-repeated-centers.md)。元の入力頭に著された nominal の根拠があり、実際の全可視候補が arity の合う変数 head である範囲。宣言一覧の順序を保持し、候補が唯一か複数かを B6・出力・中心の等式の前に判定する。繰り返す変数は、選択後に後続の実中心を最初の実中心に結ぶリテラル等式を作り、同じ fixed State にある行から head を得る。下端を中心の代わりにしない（`first_binding_at_original403`, `binder_center_batch_exact403`, `repeated_selection_mints_same_event_trace403`）。等式が見つからないだけで延期や拒否と判定しない。
- **同じ選択・出現・順序・モデル:** [変数 where](../design/dots-cycle-403-i72-variable-where.md) と [C402 組立への接続](../design/dots-cycle-403-i72-same-replay-and-typed-targets.md)。変数を直接渡し、子の関連出力を要求しない where について、元の clause 番号から実際の子の要求と捕捉を生成し、同じ State で独立に選択された子を順に結合する。該当範囲の任意の有限木で `variable_where_dictionary_sound403` を証明。さらに `concrete_source_uses_C402_exact_replay403` は具体的な選択からモデルを見ずに一つの C402 ledger を選び、その同じ ledger に対して全適合モデルの意味と固定出力の証拠を与える。
- **B6 の型木と固定出力:** `fixed_value_code_same_model403` と `retained_typed_rows_satisfy_fixed_targets403`。元の B6 位置・型木を保持したまま、値 kind のみの入れ子 nominal・record・variant・join を、同じモデルにおける固定行の右辺と照合する。照合に使う正確な等式は同じ State に実在する場合に限る。任意の型木の評価結果から保持を仮定せず、row kind の引数や旧ベクタへの強制もない。`authored_typed_rows_select_where403` と `variable_native_priority_dictionary_sound403` でこの具体的な範囲を再帰規則に接続した。
- **候補内 K2:** [著された単項共変 head の早期読み取り](../design/dots-cycle-403-i72-native-priority.md)。実際の可視候補と元の両端が一致し、共変 value のただ一つの子が構造的なパターンである場合、元の左側 port と子の実位置を対応させ、比較の成功を要求せず未絞り込みグラフで K2 を調べる。片付いていない出力の自己環が head の根拠にならなくても、既に入った位置の K2 は拒否になる（`pending_equation_still_vetoes_entered_unary403`）。混在する任意の候補・兄弟の優先順や、他の variance の訪問規則まで得たわけではない。
- **未証明の入口:** 一般の候補ごとの訪問・不一致・保留と全可視候補の一つの規則、直接の著された入力と同じ State の完成済み出力の支持の統合、B6 の実際の出力から一般の固定先等式を作って保持すること。次は現在の `SupportForest.atOriginal` と実際の型木・元の固定先を結び、少なくとも一つの完成済み出力を元の入力頭の根拠として読める規則を作る。新しい仕様判断は要求していない。I-65 Step 2/3、停止性、旧 Local/C334、fixture は対象外のまま。

## 照合

- Lean 4.35.0 で追加モジュール 8 件を `lean --trust=0 -DwarningAsError=true`、モジュール別の独立監査 8 件（42 宣言）も同じ条件で実行し終了コード 0。現れた公理は `propext`、`Classical.choice`、`Quot.sound` のみ。検証済みの全ソースを GitHub から取り直し、公開前に検証した全変更の blob と一致することを確認した。
- 技術スナップショット `9af18729b6b95cf0087e3faa236b8f3f3f0cb15f`、Lean subtree `b37d5a2ed2583a689899d3d656b2fbc79f1353fe`。23 パスの技術版差分を再照合し、この報告込みで累積 24 パス。既存の集約ファイルは import の追記だけ、凍結二ファイルは blob ID のみ確認。work/dots-main の expected-head non-force 更新だけ。固定の I-65 文・C380 チェックリストは変更なし。
- 公開ソースから別作業環境でまとめてやり直す追加コンパイルは呼び出しが中断し、完了は未確認。再試行はしていない。全リポジトリビルド、Rust、実機は未実施。使用量の枠は不明。
- 最終照合開始 `2026-11-24T23:20:48.571Z`（50 分経過）。
