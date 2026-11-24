# Yulang cycle 391

閉じた補題なし・分けた補題: S13bbb → S13bbba, S13bbbb

先頭の `addressed_semantic_ledger_to_dictionary` 一件だけ。元の三前提、結論、I-65 の固定上段は変えない。**S13bbba** は同じ実出現の原 body と capture から exact literal RHS を得る義務。**S13bbbb** は元の出力順と ordinal/target の保持を、その同じ state/model の実観測で示して辞書証拠にする義務。元の本体は `exact_rhs_to_dictionary_in_same_model addressed outputs semantic (addressed_meaning_to_exact_source_rhs addressed semantic)`。

## 検証したこと

- ordinary: 元 receipt、original `Supplies`、元出現と出力 ordinal、実 capture と fixed target を保つ。正規化した body の変換と current state に残る実 equation が与えられると、同じ model に `SourceEquation` と `Holds` を得る。explicit の original capture list と default の元 demand の位置は区別し、default の center をその実位置から導出した。
- native: 元の `.declared` と同じ typed vector を持つ actual origin が fixed target に残り、元 declared mode の contextual comparison が成立する場合、同じ model から nativeSyntax の観測と full `ContextDerives` を得る。ベクタの型/行・長さ・入れ子・点/非点を一つの scalar/center に潰さない。native は source body からこのベクタが出ることを仮定なしに示したわけではない。
- authored: 実 retained row の target で tag/constructor と arbitrary ordered evaluated value/row vector を同じ model で得る。native の非点情報へ置き換えない。どちらの観測も actual conditional retention が起点で、`Fits` やアドレスだけで保持を作らない。
- [検証済みコードと元定理の参照](https://github.com/momota1029/yulang/blob/8f1e0902d4085cd910469933e9cdfeba9d3b6bb0/notes/design/dots-cycle-391-s13bbb-rhs-and-model.md)。Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true`、C388/C390 の exact replay を依存にした。GitHub から exact code を取得し直し再実行、exit 0。ordinary/authored と合成型チェックは各 `[propext, Quot.sound]`、default capture は `[propext]`、native は既存比較経由の `[propext, Classical.choice, Quot.sound]`。合成型チェックは両未証明義務を明示した試験。新規 module・standalone import audit・全体 build・Rust は未実施。

## 残り

**14 = 未証明 3 件（S01・S10・S13bbba）+ 一部 11 件（S02–S09・S11–S12・S13bbbb）。** S13bbba の原 body/capture→任意の actual declared payload が未証明。S13bbbb は retained なら読めることまでで、一般の exact source→same-state retention と mixed dictionary 全体の意味は未証明。次の周は S13bbba の元 RHS 一件だけ。S13bba と他行は変更なし。Step 1 は未完、Step 2・3 は未着手。S1/S2 全体は閉じず、C は後回し。fixture、検査器、旧 Local/C334、停止性、言語の受理条件は変更なし。

4 パス（設計・checklist・心拍・報告）のみ `work/dots-main` に expected-head non-force。Lean tree は変更なし。凍結2ファイルは blob ID だけを照合。意味論の新しい選択や承認済みの反例は見つけていない。質問ノートなし、使用枠は不明。
- 最終照合開始 `2026-11-24T11:21:03.491Z`（50 分経過）。
