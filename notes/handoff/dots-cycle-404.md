# dots-main 第404周（I-72 / I-65 Step 1）

**閉じた補題なし・分けた補題なし。** integration の一般残件 14（未証明 3、部分証明 11）は不変。今回は「片付いた出力を同じ State の入力根拠として読む」具体的な宣言規則を実装し、その範囲の辞書健全性を証明した。一般の `Classifies` の完成ではない。

- **元の出力から元の入力へ。** [設計](../design/dots-cycle-404-completed-input.md)。同じ State にある実際の有限選択証明を `SupportForest.atOriginal` で選択証明の子から取り出し、元の出力序数の B6 型木が本当に declared nominal で、その固定先が消費側の元の下端名と文字どおり同じ場合にだけ、現在の行を根拠にする。`completed_input_owns_retained_nominal404` はこの行の保持を実際の producer 証明から導く。別の名前を同じ値として代用しない。同じ診断の pending や、固定先違いではこの証拠を作れない。
- **具体的な選択・曖昧性と健全性。** [選択と ledger](../design/dots-cycle-404-producer-consumer-ledger.md)、[全可視候補](../design/dots-cycle-404-completed-ambiguity.md)。元の候補が変数 head である範囲で、完成済みの実際の C403 出力から消費側の単項選択を導く。元の入力がすべて根拠つきで候補が複数なら、中心・B6 の出力・body で勝者を選ばず曖昧とする。複数の根拠、繰り返す実中心、元の順序の直接変数 where、既に保持された実際の型つき出力を扱う具体例では、一つの C402 ledger が全適合モデルで辞書証拠を与える（`supported_classifies_uses_one_C402_ledger404`、`finite_completed_choice_dictionary_sound404`）。C404 の選択済み木も次の producer になれる。独立した起点なしで内部の出力だけに依存する閉じた族は、有限の選択証明を持たない。実行停止性の主張ではない。
- **K2 は保持。** [範囲](../design/dots-cycle-404-completed-native-priority.md)。需要根の生の K2 は未完成の出力があっても先に拒否する。単項・宣言済み共変 value 点では、同じ固定名の完成済み外側出力が実際の子を開く場合に限り、その正確な内側 site を生のグラフで調べる。内側の未完成出力の自己環は候補を開く根拠ではないが、既に入った site で K2 を起こせる。未完成の外側出力ではその入口に入れない。追加の拒否や曖昧分岐は既存の具体的な選択証明を変えない。
- **残る正の構造 head の境界。** [正の比較](../design/dots-cycle-404-positive-completed-native-boundary.md)。正確な比較原子が普通の制約に実在する共変単項点では、完成済み下端と著された上端から、同じモデルでの型付き比較まで導いた。旧 `SourceHead` は著された下端 Origin がないこの形を表せないことも証明した。State に偽の Origin を追加せず、著された根拠と完成出力を区別する実際の head 証拠を次に表現する。一般の構造候補・根拠がないときの一般の保留・行 kind の固定先生成は未完成。
- **C402 の暫定 S03 に穴。** [記録](../design/dots-cycle-404-c402-priority-quantifier.md)。この具体例の S02 は元の選択・候補一覧・序数から作れた。しかし暫定 S03 が `visits` を拘束しない任意の `SelectedSource` に全称しているため、同じ実選択に対する空リストと一要素リストを一つの required に同一視し、実選択が存在する範囲で矛盾することを `draft_S03_over_unconstrained_visits_is_impossible404` で確認。次は元の実際の訪問導出にこの項を結びつける。固定 I-65 の文や言語仕様の反例ではなく、統合チェックリストを閉じたり分けたりしていない。新しい仕様判断は求めていない。

## 照合

- 基点: C403 `a5061fcbf7690371df862f86431ba8f716b02dc9`、指示: integration/m1-final `8cfea642b851c6b7c090cf987a481aec774c3881` の I-72、inbox blob `2684940d16dd1b4f8aa76788a2719010b04a3bf4`。
- 技術スナップショット `e4f82cde224d24bb1f63b974d540daf4f034e895`（Lean subtree `04315174826961b3f69b102494ac6c15fcf82692`）。Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）でローカルの追加 11 モジュールと独立監査 11 件が strict PASS。C404 の正確な Git バイト列を別作業ディレクトリに復元し、`lake env lean --trust=0 -DwarningAsError=true` で同じ11モジュール・11監査（56 宣言）を再実行、実際に追加した import をまとめた検査も終了 0。監査の公理は標準の `propext`、`Classical.choice`、`Quot.sound` のみ。C403 で中断した別操作は再試行していない。全リポジトリビルド、Rust、実機は未実施。使用量の枠は不明。
- work/dots-main の expected-head non-force 更新だけ。凍結2ファイルは blob ID のみ確認。固定 I-65 文・C380 チェックリストは不変。集約 Lean は import 追記のみ。技術版の累積差分 `30` パス、この報告込み `31` パス。
- 最終照合開始 `2026-11-25T00:20:43.431Z`（50 分経過）。
