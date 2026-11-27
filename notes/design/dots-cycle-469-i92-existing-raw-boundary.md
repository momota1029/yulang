# C469 / I-92 §5: 元の field はあるが同じ相の raw edge がない実例

I-92 を +10 読取りで確認した。指示 5 に従い、既存位置の参照だけでは現チェック対象の同じ raw 相に写せない例をここに記録し、**Lean を追加する前に停止**する。G04 は未完。既発行限定で閉じない。

## 実例（仕様上の非変数検査と既存 Lean の入力）

`lean/Audit/Cycle464I74ProjectedFieldActual.lean`（blob `dbb0e59bc48054d5dda7431b932fda6ca64bf957`）の `sourceOnlyInline` / `inlined`。元の request occurrence は `[71,2]`、role 19、実単一可視宣言 218（元宣言 ordinal 0）、head arg 0 の point は 4、名前付き出力は空。元 head は `{30: {40: 'a}}`。field30 の payload pattern は変数ではなく **record constructor 40**。旧 compiled metadata は実際にこの source を読み、`actual_written_closed_record_is_an_ordinary_source_head463`、`actual_inline_source_model_fits_without_named_parent_row464` と `exact_inline_candidate_is_really_prechecked463` がある。B6 atlas は空で、ここで record literal / occurrence の既存入力は authored fixture。その入力の外で B6 compiler が native row を生成した、あるいは元相の detector が既に visit を受理したとは言わない。

普通の型の略記（spec §6 の K2 L497–502 と同じ形）:

```text
μ = {40: μ}
元入力 = {30: μ}
head = {30: {40: 'a}}
required constructor visit: root の field30 にある μ
```

raw の実 snapshot は ordinary constraints と intervals がともに空、物理行は次の二本だけ。空 tail は明示の閉じた record。

```text
ordinal 0: 4 = {30: {40: var(5)}}
ordinal 1: 5 = {40: var(5)}
```

元 origin table は slot 4 の全 literal と slot 5 の exact payload（両 issuer `[402]`、direct route）を既に持つ。すなわち **issuer の欠落や native output が無いだけの例ではない**。型付け上は field30 の既存 source occurrence と terminal5 の根拠がある。実 K2 自己辺を持つ位置は 5。元の 4 では `GraphRows321.fields` が field 値 `.variable child` を要求するため `shapeOf` は none。reflexive/trans 核以外の bound generators がなく、両 rhs とも variable でないから raw Alias は等号しか導けない（`Bound` / `Alias` の帰納）。故に 4 で観測できる別 owner もない。どの既存行 ordinal・どの既存元 path を参照しても、`AuthenticatedHop458.AtStep` が要求する `shapeOf = some sh` と field30→5 の `ChildAt` はこの同相では成立しない。元の構文に 5 が書いてあること（field40 の operand）を field30 の既存 raw child と読み替えない。

元の C464 正例は別相 `independentSnapshot` に **新 raw 名ではなく新 raw 行** `ordinal 2: 4 = {30: var(5)}` を追加済みとして渡す。そこで初めて exact path `[(field30,5)]`、rows `[2]`、terminal 5 の `readProjectionField` が合格し、実証明 `same_fitting_assignments_carry_actual_projection_native_receipt` は全同じ `FitsFull` を保存する。同じ適合モデルでも raw edge/物理順位が別。I-92 の「既存の同相 raw」を満たす証拠としてこの追加行は使えない。

C466/C467 は独立の実 ordinary compiler テストとして境界を裏づける。C467 の `Cycle467I74ActualPrepareAfterCapture` では真正 C332 が target 7／raw 3 を採番し元捕捉を保つが、root4 を所有する全行の `shapeOf = none`、元 ordinary phase の Alias は反射のみ。これはまず途中の非変数 head 位置の named hop を供給しないという補助対照であり、それだけを C464 の到達端末 K2 証拠や Native360 全経路の否定にしない。

## 監督に残す表現判断

I-92 が命名を禁止した方針を維持するなら、名前を増やさない **source occurrence 上の inline 観測表現** と、既存 raw 内の terminal/実循環・非変数 visit の独立な対応証明を許すかを決める必要がある。これは「すでにある named raw edge の参照」とは別の表現である。仮想の辺を旧 raw に書き足したり、全 Model の値等式だけで old K2 を運んだりしない。既存 raw named hop に限定した正例を先に実装してこの範囲を閉じたとは報告しない。仕様・旧 checker・State、G18/GD/他行、言語の受理拒否は変更しない。
