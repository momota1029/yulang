# Ordinary parameter vs higher-order computation: read-only source audit

対象: Y2 `d4c8bc8fc`、最新仕様 integration `816ed8f1d`。親監査の `/tmp/audit3/timing-high.json` と既存コードを読む。ソース修正、独立ビルド、追加実行はしていない。

## 観測で確定すること

`our actual(x: int): int = 42` と `our higher(f) = f(ping::get())` を `abort(higher actual)` に渡すと、通常 run と interpreter はともに 42。`higher(f: int -> int)` でも同じ。これらの mono は actual 自身を `thunk[[ping], int] -> int` にして、本体を `\\d12 -> 42` のままにする。入口で force する adapter は表示されない。

同じソースの actual の本体だけを `x` にすると、mono actual は `thunk[[ping], int] -> thunk[[ping], int]` から `thunk[[ping], int] -> int` への adapter を持ち、両 runtime は abort の 99 を返す。この差は effect を使う／使わない本体によって出る。直接適用 actual(ping::get()) は親監査で 99。したがって direct と higher-order の経路で引数計算の起動が一致していない。

これは明示 `x: [_] int` / `x: [ping] int` を受ける computation 関数が未使用引数を force しない、という意図された遅延とは別である。actual の引数は普通の `x: int` である。

## コードで確定する仕組み

1. infer lowering `crates/infer/src/lowering/expr/lambda.rs:1344–1354` の `lambda_param_effect_slot` は、`AnnType::Effectful` の場合だけ fresh effect / Neg::Var を使う。それ以外は `fresh_exact_pure_effect()` と `never_neg()` を返す。つまり `x:int` 自体が明示 computation parameter として lower されるわけではない。無注釈の引数も同ファイル1251–1256で `never_neg()`。
2. specialize2 の `task_solver.rs:298–308` は concrete arg effect を持つ signature で lambda を作業する際、`lambda_expr_with_signature` を選ぶ。
3. その実体 `task_solver/control.rs:288–313` は受け取った signature の `parts.arg_effect` から `types::runtime_shape(parts.arg_effect, parts.arg)` を作り、parameter に bind する。返す Fun の arg_effect も signature 側のもの。その関数内に、元の ordinary parameter が strict だったことを保持し、入口で無条件に force する処理は見当たらない。body は期待 return shape で解かれる。
4. `task_solver.rs:605–622` の signature 無し lambda も fresh effect の runtime shape を parameter に bind する。
5. `task_solver.rs:497–512` の適用は callee arg effect が pure と確定しているときにのみ `consume_expr_value` で引数を値として消費し、その effect を呼出し結果へ加える。非pure側は `consume_expr_computation` で、call_arg_effect は pure にする。これは computation parameter を渡す場合には正しい分岐だが、普通の関数がこの側の signature に再特殊化されると、strictness の別の保持が必要になる。
6. emit `emit.rs:255–273` は引数に型境界を適用して Apply を作る。`emit.rs:865–880` は expected が Thunk なら computation を `make_thunk_from_computation` で閉じる。即座に force する規則ではない。

## 旧文書との関係

Y2 `spec/2026-06-07-principal-monomorphization.md:623–641` は、pure parameter/return は裸の runtime shape、nonempty effect は thunk とし、apply では callee parameter shape が thunk なら argument computation を MakeThunk で閉じると明記している。したがって runtime の thunk passing 自体は旧文書どおりであり、それだけを不具合と呼べない。

Y2 `web/docs/ja/reference/effects.md:174–186` の compose の記述では `x: [_] _` を「第三引数が computation」と明示している。一方、普通の関数を高階の要求に合わせて再特殊化するとき、入口で未使用引数も起動すべきかをこの引用だけでは定められない。普通の引数と明示 computation の区別を消してよいという根拠でもない。

最新版 `spec/05-effects.md` §5.5c は、普通の関数を effectful argument の場所へ使う cast について、**関数の起動時に引数の計算の効果を放出する**と確定している。よって ordinary ignore が higher-order 経由で 42 となる Y2 実測を、その新仕様の cast の意味の証拠として使ってはいけない。起動時に ping を実行するなら非再開 handler の 99 となるはずであり、この対照は新仕様への conformance gap として報告できる。

## 原因の確定範囲

確定: 最終 mono の ordinary actual parameter は thunk に変わり、本体 ignore の入口には無条件 force がない。VM/interpreter の両方で未使用計算を飛ばす。infer は ordinary parameter と explicit effectful parameter を区別している。specialize2 の consumer signature ベース lambda 特殊化は thunk parameter へ bind できる。

強い候補: higher-order demand を使う lambda 再特殊化が ordinary strictness を失い、computation-taking 関数として直接再構築している。未使用 parameter では戻り値の force adapter も生じないので ping が起動されない。identity は戻り側 adapter が偶然 force するため 99 になる。

未確定: この具体入力の全 solver slot / demand provenance を instrument したわけではなく、どの signature 発生地点が最初に ordinary arg effect を非pureへ変えたかは未追跡。上記候補を単一行の確定 root cause、または修正済みと報告しない。既存 F1 `[ping] vs []` compile failure と同じ root causeとも断言しない。
