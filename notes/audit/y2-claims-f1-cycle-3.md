# Cycle 3 F1・効果の起動時点の監査

基点: 新spec `816ed8f1d`、旧実機 `d4c8bc8fc`。以下は具体例の分類であり、全言語のsoundness/completeness/principalityを主張しない。コマンド全文とsource/outputは `runtime-cycle-3-f1*.md`、`runtime-cycle-3-timing*.md`、source追跡は `f1-source-cycle-3.md` と `f1-timing-source-cycle-3.md`。

新§5.5cはF1を**独立cast判断**と確定済み。標準arrow subtypeの `Common.common_arrow_iff` に特例がないことをそれ自体の欠落とは分類しない。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新 spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C3-F1-01 | effects.md関数適用、infer propagate.rs212–259 | 普通の関数に効果引数を渡すと起動時に引数を評価する | `ignore(x:int)=42; abort(ignore(ping()))` | no-prelude check/poly/mono/run0、非再開handler99。resumeなら42 | 5.5c | CommonSyntax.Typing.strictApp、CommonCoreStrictApplication.forceApplication | 一致 | 使用しない引数でも直接呼出は起動。abort/resume対照。 |
| C3-F1-02 | 同上、高階適用 | 普通の関数が高階引数として要求されても起動時の引数効果を保存するか | `higher f=f(ping()); abort(higher ignore)` | check0、mono0、VM/interpreterとも42 | 5.5cでは起動時放出なので99が期待 | strictAppの局所効果合流だけでは独立cast挿入・source接続を証明しない | 違う | ordinary `x:int` を使用。明示computation parameterの意図された遅延とは別。 |
| C3-F1-03 | 同上 | 高階の引数を実際に使う場合 | `actual(x:int)=x; higher f=f(ping())` | abortでVM/interpreterとも99、resumeで7 | 5.5c | ordinary→computation castのsource-to-runtime証明は未確認 | 一致 | identity成功だけではunused argumentを含むF1全体の証拠にならない。 |
| C3-F1-04 | infer propagate.rs; specialize2 task_solver.rs/type_graph.rs | 明示effectful戻りを持つ関数の高階消費 | `higher(f:int->[ping]int)=f(ping())` | pure/実effectful/literal/unreachable effect actualすべてcheck/poly0、mono/run1 `[ping] vs []` | 5.5c | Common arrowは標準関係で正当。独立castのこのsurface境界は未確認 | 違う | pure actualだけのadapter失敗とは限定できない。slot provenance未追跡。 |
| C3-F1-05 | 同上 | 高階消費でも実引数がpureの場合 | `higher(f:int->[ping]int)=f 3` | 4 actualでcheck/poly/mono/run0、3/7/3/3 | 5.5c | 上記局所判断のみ読取 | 一致 | C3-F1-04の差はこのmatrixではeffect argumentとの組合せに局在。 |
| C3-F1-06 | effects.md effect variable、type ascription | 単一bindingのascription、戻り行変数、明示empty戻り行 | `my f:int->[ping]int=plain; f(ping())`、`higher(f:int->['e]int)` | 各check/poly/mono/run0、handlerで7 | 5.5c | source接続未確認 | 一致 | このfinite matrixの成功。全annotationの主型性ではない。 |
| C3-F1-07 | application.md、syntax-style.md pipe | pipeでも普通の関数の未使用引数を起動 | `abort(ping() | ignore)` | check/poly/mono/run0、99 | 3.9、5.5c | core strictApp。surface pipeの導出未確認 | 一致 | 今回は一引数なので旧/新のpipe引数位置差は無関係。 |
| C3-F1-08 | functions.md curry | partial applicationの第一引数の効果は、その第一段階の起動時 | `second(x:int)(y:int)=y; abort(ignore_fun(second(ping())))` | check/poly/mono/run0、99。lambda bodyに包めば42 | 3.3、5.5c | source curry/cast bridge未確認 | 一致 | 結果の関数を捨てても第一引数は起動、未適用lambda本体は起動しない。 |
| C3-F1-09 | control-flow.md block | blockの未使用let/bare statementも順次評価 | `f()= {my x=ping();42}` | abort99、resume42、check/poly/mono/run0 | 3.5 | Core block/source loweringの対応未確認 | 一致 | bodyでxを使わない対照。 |
| C3-F1-10 | specialize2 control.rs288–313、emit.rs865–880 | consumer signatureによりlambda parameterをthunk形へ特殊化する | `higher ignore` のmono | ordinary actualがthunk[[ping],int]→int、本体42、入口forceなし。identityは戻りadapterがforce | 5.5cのordinary起動時放出との接続が必要 | 独立cast判断と旧specializerを同一視しない | 違う | 観測と静的経路は確認。ordinary strictness喪失は強い原因候補だがdynamic demand trace未実施。 |
