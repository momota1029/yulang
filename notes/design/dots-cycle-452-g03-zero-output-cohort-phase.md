# C452 / G03: 空の出力等式発行と、原位置を残す内部 K2 記録

正本 `integration/m1-final@76a9a16da8d6647ae9bb303f386bdbca44cb75c5`。spec §6.3 は同 role かつ全入力の同一性で併合する。C451 の実元位置・同 role・raw Alias が正の十分条件となる場合だけを扱う。値の同値や端点一致・証拠の失敗を一般の同一性・非併合には使わない。

- 入力は同じ FullProblem の実選択済み C450 親、各 literal where の元出現と真の捕捉、C451 のその raw graph における exact 類と各根の K2。独立な証拠から有限 wire を反映する。
- 各群の member は実宣言の元 clause 番号の `SourcePointAt` を持ち、同群の二つは実 `SameInputs`。全適合モデルを保ったまま、既存の `GeneralNominalDemandMerging.outputAtoms` をその二つの実 site に適用する。子 demand に出力の指定が一つも無いため、この等式発行サブステップのバッチは空で、ordinary は等しい。C324 center alignment やドライバ全体を実行したとは仮定しない。
- 後段は検査された cyclic 類につき内部 K2 エントリ一つと全元位置を保持し、類の中の元順序を保つ。外部の代表位置・全体の表示順・canonical report は定めない。旧 literal trace と併置するときは旧 carrier の子数を縮めない。raw-safe な兄弟の選択は別の独立な authored leaf read が要る。
- 予定する検証: 全元 mark を実 site に戻せること、既存正確な出力等式操作の空バッチと raw 同一性、任意の実元位置の根 K2 と内部エントリの一対一対応、独立な scope 証拠の exact replay。実同 role の二つの cyclic 節と非 cyclic な別類を含め、表示選択はしない。
- C451 の表示位置の問いは保留。同一性の一般形式・非空出力・構造引数から actual phase への接続 G15–16 は未証明。G03 全域と現行累積 checker は変更しない。
