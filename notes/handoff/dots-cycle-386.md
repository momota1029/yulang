# Yulang cycle 386

この周に閉じた補題: S13a（general_literal_replay_alignment）

I-68 の先頭の一件だけを閉じた。元の `literal : t = dictionaryTree d` と、同じ選択の `replay : LiteralTreeFrom tree t lowered` から、`CanonicalDictionaryReplay replay` を得る。独立な source 判定 interface のすべて、任意の `State`・要求・辞書・記録列、任意の有限の where 木と兄弟列で成立。追加のモデル、型の意味、局所健全性、release、選択の一意性は仮定しない。

## 証明が保存するもの

- `GeneralDeclarativeI65LiteralReplay386.lean`: 同じ source event データを trace と lowered tree の両側の構成子に置く。実宣言一覧の ordinal と宣言、元 where clause の ordinal と順序、全要求の出現、元 output ordinal/name/target を保持する。型付き出力は unary に限らず、literal 構文と任意長の value/row ベクタ（point と nonpoint）をそのまま持つ。元の ordinary 等式を別の同値な行に取り替えない。局所 source 判定と event の関係は独立 interface として保持し、S01 の規則をここで定義しない。
- `GeneralDeclarativeI65CanonicalReplay386.lean`: paired replay の tree/forest への相互帰納で元 event の ledger を作り、同じ event を source trace と lowered tree にそれぞれ突合する。子の本数と元順に対応する canonical tree を得て、親の literal receipt 列、次に子の列を順に連結した等式を返す。出力が空の節点は ledger から落とさない。元 event は `Prop` の証明同一性や辞書 key の等しさから再構築しない。
- `ReplayJudgment` は未実装作業名 `LocalSource` と、その原始導出がこの同じ event を許す関係を持つ。定理の暗黙 context はこの interface に全称で、表示上の固定二前提以外に alignment 済み、意味済み、あるいは全状態の選択の一意性を付け足していない。実際の言語の `Classifies`、同じ event のモデル意味を辞書へ包む S13b、最上段の `dictionary_sound` はまだ証明していない。

## 残り

**未解決 13 件 = 未証明 3 件（S01、S10、S13b）＋ 一部 10 件（S02–S09、S11、S12）。** S13a 一件だけを減らした。S13b は次の対象だが今周は手を入れていない。S01–S12、S13 の親定理、S13b、固定 `dictionary_sound`・`check_sound` と最上段の合成は byte-exact に維持。Step 1 未完、Step 2・3 は未着手、S1/S2 未完、C は後回し。停止性、旧 `Local`、旧 C334、fixture、言語の受理範囲・K2・物理権限に変更なし。承認済み言語例の仕様上の順依存は確認しておらず、意味の質問は起票していない。

## 検証・公開

- 開始 `2026-11-24T05:30:32.156Z`。前周 `51fa4b658cde9132f5999a98a4f199ebb0b7b09b` の完了心拍・報告と、正本 `a8bcdab34923b36ca589abe8ed6bf94bc00665e6` の常設指示、inbox `8fcff32329234b9cc304a919051d1c30e03542aa`、役割／推論仕様を照合した。前周の正本からこの正本まで Lean 差分なし。既存の精査済み S13 replay 閉包は同じ bytes。
- Lean 4.35.0、2モジュールを `lean --trust=0 -DwarningAsError=true -o …`、独立 `Audit/Cycle386CanonicalReplay.lean` を `lake env lean --trust=0 -DwarningAsError=true …` で実行。Git に載せた3ファイルの exact bytes を別出力先に取り直し、2モジュールと同監査を再実行してすべて exit 0。監査で一般定理の二前提・全称の型を表示。定理は `propext`・`Quot.sound` のみ、carrier もその範囲。全体ビルド、CI、Rust、全言語の Step 1 テストは実施していない。
- 技術 pin `d9c995bc155d07ac0144b494f0302aaa1f62f7d8` / Lean tree `852b0e77368843a113583814d2793449aa3499cf`。公開は `work/dots-main` のみ expected-head / non-force。累積 7 paths（Lean 2、独立監査 1、barrel 1、一覧 1、心拍 1、報告 1）。barrel は元 bytes に import 2行のみ追記。凍結2ファイルは blob ID のみ確認。使用量の枠は不明。
- 05:56 UTC 頃に実行環境が不可になった時点で、上記の Lean 検証と Git exact bytes での再実行は既に完了していた。それ以降は GitHub からの読み戻しと報告だけを実行した。
- 最終照合開始 `2026-11-24T06:20:41.379Z`（50 分経過）。
