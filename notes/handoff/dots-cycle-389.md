# Yulang cycle 389

閉じた補題なし・分けた補題: S13bb → S13bba, S13bbb

I-68 の `exact_semantic_ledger_to_dictionary` 一件だけを分けた。元の四前提と結論、上段の定理と組立を維持。**S13bba** は replay を実要求と実辞書の出現へ結ぶ。**S13bbb** はその同じ ledger の具体的な局所意味から、同一モデルの fixed output をもつ辞書証拠を作る。

## 検証したこと

- 実際の lowered が持つ `LoweredEventLedger` から同じ event・guard、full `Request`、実 `Dictionary.node` の子辞書と event の where 子の順を再構成できる。そこから canonical diagnostic の key/子順も得る。その exact 出現を別の辞書キーや receipt 列の一致で置き換えない。
- C386 の `receiptAt` が確認する occurrence/ordinal/要求/`Supplies`/target は、同じ target で declared `Pattern` と任意の型/行引数ベクタを差し替えても維持される。従ってこれらのフィールドだけでは、指定された source body と actual capture が元の typed payload を生成したことを示さない。**source guard の保持は示していない**。承認された言語の反例でも、書き込み順や受理を変える結果でもない。
- 型を合わせた元の組み立ては `addressed_semantic_ledger_to_dictionary (exact_replay_ledger_addresses eventMatch) outputs semantic`。canonical 順は住所の証拠から得られ、元の四前提は削除しない。後半は独立義務として残す。
- [厳格検証したコードと source anchors](https://github.com/momota1029/yulang/blob/d306aaddfe45ff032d3152884548dd18ea90c915/notes/design/dots-cycle-389-s13bb-addresses.md)。Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true`（C388 の exact replay output を依存に使用）。GitHub から同じ immutable 設計ノートを取得してコードを再実行、exit 0。addresses と receipt field は各 `[propext]`、canonical order と合成型検証は各 `[propext, Quot.sound]`。新規 Lean モジュールへの登録、独立 import audit、全体 build、Rust は実行していない。

## 残り

- S13bba は exact 文の `--stdin` 検証まで。次の周はここだけを module + audit として検証。S13bbb は未証明。普通の `Holds` に加え、実 `Supplies`/actual capture から typed 値/行・点/非点・入れ子の payload を確定し、その出力が元の ordinal/target に同じ State の真正な観測として残る関係が必要。`Fits`、canonical shape、tagged unary point の既存断片だけでは一般には足りない。scope が確認できない部分の新しい意味や拒否方針は定めない。
- **14 = 未証明 3 件（S01・S10・S13bbb） + 一部 11 件（S02–S09・S11–S12・S13bba）。** 未解決一件を二件に分けたため +1。S13ba と他の S 行は変更なし。Step 1 は未完、Step 2・3 は未着手。S1/S2 全体は閉じず、C は後回し。停止性・旧 Local・旧 C334・fixture・検査器は手を入れていない。
- 変更は設計、checklist、heartbeat、報告の 4 パスだけ。Lean tree は同一。凍結ファイルは blob ID のみ照合。発行は expected-head non-force の `work/dots-main` のみ。質問ノートなし、使用量の枠は不明。
- 最終照合開始 `2026-11-24T09:20:53.696Z`（50 分経過）。
