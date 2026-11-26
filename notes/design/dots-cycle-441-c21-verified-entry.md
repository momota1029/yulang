# C441 — C21 の順序付き row/value ref 検査

正本 `2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5` は前周 C440 exact。I-74 の C21 一行だけ。`RefPositions441` の新規 source rule は実候補の `ref _ 'a` （別々の binder、singleton、where/出力なし）。最初の引数は依存しない raw value slot としてではなく `RowTerm` の row atom と符号つき行の値、二番の引数は value の atom/capture。両方とも元の origin と元の候補の ordinal から読む。本文の owner と source-side 順序を保つ。

- 変数の順は `[row,covariant; value,invariant]`。§4.6 `run` の既知の公開 `'e` は出力側、`'a` は callback の入出力双方。フィールドで束縛される `'f` は型パラメータに追加せず、mode に関係する公開部分を実 typed body graph に下げて計算した。rank-2 `run` の完全な lowering ではない。
- 元の `SourceHead`（順序付き `DeepHead.declared`）と実 `ModeWindow`/`DeepRead` を通り、新しい同じ状態の有限 `SourceTrace` を得る。すべての適合モデルで既存 `DictionaryEvidence.node`、二つの typed capture を保つ。where と固定出力はこのケースでは空で、古い定義には手を加えていない。
- `R21`、`dictionary_sound_R21`、データだけの `.reference` 分岐、固定外形 `check_sound` を追加。旧 witness の Boolean は全て同じ。raw graph は author によって filter せず、元の root K2 が古い拒否として優先する。両葉は binder なので触らない。exact kinded native origin の検査であり、row を legacy raw `.nominal` の value として偽装しない。
- 実 fixture で signed occurrence `(56,[1,-2])` を row slot 1 で保持し、value slot 2 は Int（その row は空）、実辞書・適合モデルあり。mode 順交換、endpoint 順交換、binder を使い回す入力、実可視 rival、issuer や report の違いは現新分岐で false。実 raw-root-cycle は old true/new false。literal `ref _ int` の元の Problem は構成できるが binder 専用分岐は false。これは言語の拒否を意味しない。exact literal matcher と B3 の rank-2 は未完。
- 公式 Lean 4.35.0 strict（`--trust=0 -DwarningAsError=true`）。4 production、独立 Audit 5 本を個別、30 audit 宣言標準のみ。全体 build/Rust は行っていない。
