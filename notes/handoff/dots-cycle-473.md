# dots-main handoff: Cycle 473

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- Scheduled 2026-11-27 20:30 UTC; actual start 20:30:04.633 UTC; normal gate 21:20:04.633 UTC; hard cap 21:25:04.633 UTC。
- Authority `integration/m1-final` `3984c7d8d805c766e19254dcd70633b61d800fd2`、I-93/I-94 inbox `cc5401e2d3218d6ea5b088aa51aeb453f8706396`。C471 のコメント修正と C472 が、元 work terminal と同じ Lean tree `1bc8ae0586c0b10b81bd1b30bf1fa37695ff1c3e` として採用済み。修正の再適用なし。I-93 は yulang3 `dc1a72790204b5d68fd8ededa47ea50aefcf9556` の仕様 §6.3 と同じ（roles blob `a3d903781fef0691b773f886ba8976a6b4ac871d`）。
- C473 の科学差分は `975537174bc687cd61b6e991c593bf1b0ff99363` で固定。Lean tree `c6402e35b0f6b6392296fd5bdba6c4207cc0bdeb`。[設計](../design/dots-cycle-473-literal-observation-path.md)。

## 証明と実例

- `EquivalentObservations473`: 有限の到達範囲で、指定した旧 Alias 類の全実定義を読む。比較に使う関係の両端についても別の定義を見落とさない。対応関係は各構成子と順序付きの子を照合し、有限展開の書き方だけが違う実例が同じ元 field を返す。関係不足では未確定。
- `LiteralVisitCoordinates473`、`CheckedObservationPath473`: 元の構文、正規化後の実 compiler query、既存 raw 行中の選択子を分け、選択した非変数構成子だけを構造帰納で辿る。最初の field と深い位置は格納済み inline、変数から名前つき owner に飛び越えない。実際の外側引数と続行する手前はそれぞれ商で安全と確認。実例の深い field は循環、外側と中間 field は安全で、循環値への単なる到達を拒否と取り違えない。
- `FiniteCheckedObservation473`、`IndependentPathReplay473`、`IndependentPathReflection473`: 固定の観察表・対応関係と完全な到達コーン（実定義と関係端の照合を含む）では、両符号は正確な有限 witness を持つことと同値。独立の有限経路と reader の往復は、実際の元 path、終端、符号を保つ。
- `AuthenticatedPathReplay473`、`AuthenticatedPathSound473`: 実際の元 occurrence・宣言 ordinal・head と、別途確証された同相の入力 source と C332 読取りから exact report を再生し、成功から逆にも回収する。元 raw の同じ全 `FitsFull` でその source 読取りが成り立ち、符号は報告した終端で等しい型へ非空で戻ること。完了の有無にかかわらず、出力だけの物理行からこの入力結果は返らない。
- `C332SourceErasure473`: 既存 C332 が実際に受け取るものと戻す捕捉を切り分けた。同じ元 head・code・lower・raw 行なら、元物理位置と著者位置が別でも捕捉だけでは区別できない。実際に raw 0/4 と著者表 0/2 の二つの組で、同じモデルが適合し同じ binder 3・var 6 を読む。誤った ordinal は失敗。どちらかを現行 compiler が発行したと仮定しない。

## 検証と次

- 新規 production 9、standalone Audit 10 と集約の末尾 import 9。既存ファイルはこの末尾追記以外不変。公式 Lean 4.35.0 の `--trust=0 -DwarningAsError=true` で焦点を絞った exact byte 再生を行い、31 の公理照会は標準集合の範囲、5 組の実行 guard は期待どおり。追加 import を独立照合。公式 verifier の追加行字句と I-94 の単語境界を実際の authority 差分の 20 Lean パスで検査し、禁止語 0、5 `#eval` はすべて guard つき。全 Lake・Rust・監督役の統合検証本体は実行していない。
- 旧 Yulang2 は現行判定に読み替えない。既存 oracle `0d75bdb801151589d5aeef453fd6b7dfa414baec` の X8/X9 は構造 μ の出力なし、X10 は空 record-head impl dump まで、X11 は parser 失敗。実機の再実行なし。
- **G04 未完了、残り 20/24。** 同相の単一候補・事前検査済み GD、別供給の入力 provenance、閉構文と検査済みの観察を対象とした追記。旧 raw の名前・行、既存の checker、言語仕様は変更していない。現行の要求入力の compiler event から正しい source 表と元物理位置を得る橋はまだない。C332 の捕捉の結果だけでその橋を置き換えられない。G05/G10、G08、GD、G06/G07、G20/G21 は未着手。
- 次回は inbox を再読し、compiler が元 occurrence と物理行をまだ同時に持つ場所から証拠を取り出せるかを先に確認する。到達観察の生成と元の入力権限を区別し、書込みや存在しない発行者を作らない。新しい意味論の質問は積んでいない。
