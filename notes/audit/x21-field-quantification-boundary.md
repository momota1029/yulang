# X21 holder field-rigid 追加監査

2026-11-08 UTC。新 spec integration 3fdd6c3acac223b0920730979b3fd01b94366509、旧 Y2 d4c8bc8fc8a49173180932cd25921a2c41057354。リポジトリ変更なし。

## 結論と主張の限定

`struct holder { run: 'a -> 'a }` の定数関数受理は、新 spec 04-types.md §4.6 の**全ユーザー struct に適用される構築時 rigid 検査規則との観測差**である。一方、旧 Y2 が field-local forall を実装した上で rigid 検査だけを誤っているとは主張しない。実際の `--poly-raw` では constructor と accessor のそれぞれが独立な**外側 scheme**に量化子を持つ。これを新仕様と同じ rank-2 型だと解釈して比較するのは不正確である。

新仕様の限定:
- struct の明示型引数に無く、field 型だけに現れる変数が field 内で全称量化される。対象はすべてのユーザー struct。
- 構築時 rigid、field を取り出すたび具体化。
- lambda 引数の多相性は別の未決事項。
- forall field の部分型比較、一般化との相互作用、role 解決との相互作用は未決。
- 今回の holder 引数は単相な nominal holder であり、lambda 引数そのものを高階多相にする要求ではない。

## 追加 8 例（24 check/dump/run 呼出）

全 check/dump は exit 0。完全な入力・コマンド・出力は followup-raw.md/json。

|例|run 結果|意味|
|---|---|---|
|h=holder{run:identity}; (h.run 1,h.run "x")|exit0 `(1,"x")`|正例。同一 holder で別型利用|
|h=holder{run:constant1}; 同上|exit0 `(1,1)`|新 rigid 規則なら構築時拒否すべき負例|
|twice(h:holder)=(h.run 1,h.run "x"); twice(identity holder)|exit0 `(1,"x")`|正例。引数として受け取る同一値|
|同 twice に constant1 holder|exit0 `(1,1)`|twice の dump は `holder -> (int, std::text::str::str)`。my h の一般化だけに帰せない差|
|make(y)=holder{run:lambda x.y}; h=make 7; 二回利用|exit0 `(7,7)`|捕獲変数も構築時の rigid 検査を受けるべき負例|
|計算式で identity holder を返して h に束縛、二回利用|exit0 `(1,"x")`|my h が値構文かどうかだけで説明しない対照|
|constant1 holder を作るだけ、未使用|exit0 holder closure|利用制約が原因でない構築受理|
|明示引数 `struct holder 'a {run:'a -> 'a}` の constant1、二回利用|exit1 `conflicting type candidates: std::text::str::str vs int`|新 field-local 規則の対象外の対照。同じ表記変数でも扱いが違う|

## raw scheme と実装

`followup-poly-raw.txt` は constant1 holder を twice に渡す例の全 raw dump。

constructor d0: outer `scheme { quantifiers: ['3] ... }`; result `Con(holder, [])`; parameter `Record(run: Fun(... Var('3) ... Var('3)))`。
accessor d1: outer `scheme { quantifiers: ['5] ... }`; predicate `holder -> ('5 -> '5)`。
よって表示は概念上 `forall a. {run:a->a}->holder` と `forall b. holder->b->b` に対応し、`{run:forall a.a->a}->holder` という field-local binder の表示ではない。

ソース読取:
- `crates/infer/src/lowering/body/type_decl.rs:367–416` は明示 owner 引数の fresh var と payload signatures から通常 constructor function を生成。
- `lowering/constructor.rs:220–264` は field を lower_data_neg し通常 subtype 制約を追加。
- `lowering/mod.rs:849–865` の signature_var は未登録の注釈変数を fresh type var にする。
- `lowering/body/type_decl.rs:239–297` は別に field accessor 型を生成。

既存テストの読取（この追加監査では実行していない）:
- `lowering/tests/case_01.rs:376` struct_constructor_lowers_to_scheme は明示 Box 'a の scheme.quantifiers.len()==1。
- 同 :398 type_with_self_struct_lowers_outer_constructor_scheme も明示型引数の outer scheme を検査。
- `case_03.rs:1501` struct_field_lowers_to_value_method_selection は field 射影を独立 method scheme に解決することを検査。
これらは field-local rank2/rigid のテストではない。限られた検索で見つからないことをリポジトリ全体で存在しない証明とはしない。

旧文書 `web/docs/ja/reference/types.md:103–122` は値制限/外側 scheme と、複数型で呼べるだけでは一般化を確認できないことを明記。今回も正例の呼出成功のみを rank2 実装の根拠にしない。

## X21 全体への帰結

主分類「実機で表せない」は維持。元 ref/sub/YadaYada の完全例を再現したわけではなく、高階 effect binder の受け渡しを確認したわけでもない。備考に上記の新 spec 4.6 との限定した観測差を追記できる。『旧実装の rank2 の反例』『X21 全体が反証された』とは書かない。

raw dump の最初の呼出だけ YULANG_CACHE_DIR 未指定で既定 cache 作成警告が出た。dump exit は 0。その他24呼出は明示 cache dir を使用。既存ファイル変更/削除なし。
## rigid-follow-id-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-id-twice.yu
```
exit=0
```text
```

## rigid-follow-id-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-id-twice.yu --poly
```
exit=0
```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:r1:x->d4:x)})
root exprs e13:(e8:(e6:(e5:r2:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r3:h->d3:h.s1.run->d1) e11:"x"))
runtime roots d3:h e13:(e8:(e6:(e5:r2:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r3:h->d3:h.s1.run->d1) e11:"x"))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}
```

## rigid-follow-id-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-id-twice.yu
```
exit=0
```text
run roots [(1, "x")]
```

## rigid-follow-const-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-const-twice.yu
```
exit=0
```text
```

## rigid-follow-const-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-const-twice.yu --poly
```
exit=0
```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:1)})
root exprs e13:(e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r2:h->d3:h.s1.run->d1) e11:"x"))
runtime roots d3:h e13:(e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r2:h->d3:h.s1.run->d1) e11:"x"))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}
```

## rigid-follow-const-twice
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-const-twice.yu
```
exit=0
```text
run roots [(1, 1)]
```

## rigid-follow-id-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> x})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-id-arg.yu
```
exit=0
```text
```

## rigid-follow-id-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> x})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-id-arg.yu --poly
```
exit=0
```text
roots d0:holder d3:twice
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:twice: holder -> (int, std::text::str::str) = e9:(fn p0:d4:h -> e8:(e3:(e1:(e0:r0:h->d4:h.s0.run->d1) e2:1), e7:(e5:(e4:r1:h->d4:h.s1.run->d1) e6:"x")))
root exprs e16:(e10:r2:twice->d3:twice e15:(e11:r3:holder->d0:holder e14:{run: e13:(fn p1:d6:x -> e12:r4:x->d6:x)}))
runtime roots e16:(e10:r2:twice->d3:twice e15:(e11:r3:holder->d0:holder e14:{run: e13:(fn p1:d6:x -> e12:r4:x->d6:x)}))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:h arg
  d6:x arg
}
```

## rigid-follow-id-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> x})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-id-arg.yu
```
exit=0
```text
run roots [(1, "x")]
```

## rigid-follow-const-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> 1})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-const-arg.yu
```
exit=0
```text
```

## rigid-follow-const-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> 1})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-const-arg.yu --poly
```
exit=0
```text
roots d0:holder d3:twice
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:twice: holder -> (int, std::text::str::str) = e9:(fn p0:d4:h -> e8:(e3:(e1:(e0:r0:h->d4:h.s0.run->d1) e2:1), e7:(e5:(e4:r1:h->d4:h.s1.run->d1) e6:"x")))
root exprs e16:(e10:r2:twice->d3:twice e15:(e11:r3:holder->d0:holder e14:{run: e13:(fn p1:d6:x -> e12:1)}))
runtime roots e16:(e10:r2:twice->d3:twice e15:(e11:r3:holder->d0:holder e14:{run: e13:(fn p1:d6:x -> e12:1)}))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:h arg
  d6:x arg
}
```

## rigid-follow-const-arg
```yulang
struct holder { run: 'a -> 'a }
my twice(h: holder) = (h.run 1, h.run "x")
twice (holder {run: \x -> 1})
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-const-arg.yu
```
exit=0
```text
run roots [(1, 1)]
```

## rigid-follow-capture
```yulang
struct holder { run: 'a -> 'a }
my make(y) = holder {run: \x -> y}
my h = make 7
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-capture.yu
```
exit=0
```text
```

## rigid-follow-capture
```yulang
struct holder { run: 'a -> 'a }
my make(y) = holder {run: \x -> y}
my h = make 7
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-capture.yu --poly
```
exit=0
```text
roots d0:holder d3:make d4:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:make: any -> holder = e5:(fn p0:d5:y -> e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p1:d6:x -> e1:r1:y->d5:y)}))
my d4:h: holder = e8:(e6:r2:make->d3:make e7:7)
root exprs e17:(e12:(e10:(e9:r3:h->d4:h.s0.run->d1) e11:1), e16:(e14:(e13:r4:h->d4:h.s1.run->d1) e15:"x"))
runtime roots d4:h e17:(e12:(e10:(e9:r3:h->d4:h.s0.run->d1) e11:1), e16:(e14:(e13:r4:h->d4:h.s1.run->d1) e15:"x"))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d5:y arg
  d6:x arg
}
```

## rigid-follow-capture
```yulang
struct holder { run: 'a -> 'a }
my make(y) = holder {run: \x -> y}
my h = make 7
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-capture.yu
```
exit=0
```text
run roots [(7, 7)]
```

## rigid-follow-id-computed
```yulang
struct holder { run: 'a -> 'a }
my h = (\x -> x) (holder {run: \x -> x})
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-id-computed.yu
```
exit=0
```text
```

## rigid-follow-id-computed
```yulang
struct holder { run: 'a -> 'a }
my h = (\x -> x) (holder {run: \x -> x})
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-id-computed.yu --poly
```
exit=0
```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e7:(e1:(fn p0:d4:x -> e0:r0:x->d4:x) e6:(e2:r1:holder->d0:holder e5:{run: e4:(fn p1:d5:x -> e3:r2:x->d5:x)}))
root exprs e16:(e11:(e9:(e8:r3:h->d3:h.s0.run->d1) e10:1), e15:(e13:(e12:r4:h->d3:h.s1.run->d1) e14:"x"))
runtime roots d3:h e16:(e11:(e9:(e8:r3:h->d3:h.s0.run->d1) e10:1), e15:(e13:(e12:r4:h->d3:h.s1.run->d1) e14:"x"))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
  d5:x arg
}
```

## rigid-follow-id-computed
```yulang
struct holder { run: 'a -> 'a }
my h = (\x -> x) (holder {run: \x -> x})
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-id-computed.yu
```
exit=0
```text
run roots [(1, "x")]
```

## rigid-follow-unused-const
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-unused-const.yu
```
exit=0
```text
```

## rigid-follow-unused-const
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-unused-const.yu --poly
```
exit=0
```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:1)})
root exprs e5:r1:h->d3:h
runtime roots d3:h e5:r1:h->d3:h
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}
```

## rigid-follow-unused-const
```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-unused-const.yu
```
exit=0
```text
run roots [holder({run: <closure>})]
```

## rigid-follow-explicit-param
```yulang
struct holder 'a { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/rigid-follow-explicit-param.yu
```
exit=0
```text
```

## rigid-follow-explicit-param
```yulang
struct holder 'a { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/rigid-follow-explicit-param.yu --poly
```
exit=0
```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder 'a = <missing>
my d3:h: holder('a | int) = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:1)})
root exprs e13:(e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r2:h->d3:h.s1.run->d1) e11:"x"))
runtime roots d3:h e13:(e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r2:h->d3:h.s1.run->d1) e11:"x"))
detached {
  d1: holder 'a -> 'a -> 'a = <missing>
  d2: std::control::var::ref('a, holder 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}
```

## rigid-follow-explicit-param
```yulang
struct holder 'a { run: 'a -> 'a }
my h = holder {run: \x -> 1}
(h.run 1, h.run "x")
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/rigid-follow-explicit-param.yu
```
exit=1
```text
conflicting type candidates: std::text::str::str vs int
```

## poly-raw output
```text
raw roots [d0:holder, d3:twice]
raw root exprs [e16]
raw runtime roots [e16]
defs {
  d0:holder = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: ['3]
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Var('3)
          p1 = Bot
          p2 = Con(holder, [])
          p3 = Fun { arg: n4, arg_eff: n5, ret_eff: p1, ret: p2 }
          n0 = Top
          n1 = Row([], tail: n0)
          n2 = Var('3)
          n3 = Fun { arg: p0, arg_eff: p1, ret_eff: n1, ret: n2 }
          n4 = Record(run: n3)
          n5 = Bot
      }
  d1 = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: ['5]
        stack_quantifiers: []
        predicate: p6
        types:
          p1 = Bot
          p4 = Var('5)
          p5 = Fun { arg: n7, arg_eff: n1, ret_eff: p1, ret: p4 }
          p6 = Fun { arg: n6, arg_eff: n5, ret_eff: p1, ret: p5 }
          n0 = Top
          n1 = Row([], tail: n0)
          n5 = Bot
          n6 = Con(holder, [])
          n7 = Var('5)
      }
  d2 = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: ['7, '8]
        stack_quantifiers: []
        predicate: p11
        types:
          p1 = Bot
          p7 = Var('7)
          p8 = Var('8)
          p9 = Row([])
          p10 = Con(std::control::var::ref, [u0, u4])
          p11 = Fun { arg: n9, arg_eff: n5, ret_eff: p1, ret: p10 }
          n0 = Top
          n1 = Row([], tail: n0)
          n5 = Bot
          n8 = Var('7)
          n9 = Con(std::control::var::ref, [u0, u1])
          n10 = Var('8)
          u0 = Bounds(p7, n8)
          u1 = Con(holder, [])
          u2 = Bounds(p8, n10)
          u3 = Bounds(p9, n1)
          u4 = Fun { arg: u2, arg_eff: u3, ret_eff: u3, ret: u2 }
      }
  d3:twice = Let { vis: my, body: e9, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p15
        types:
          p1 = Bot
          p12 = Con(int, [])
          p13 = Con(std::text::str::str, [])
          p14 = Tuple([p12, p13])
          p15 = Fun { arg: n6, arg_eff: n5, ret_eff: p1, ret: p14 }
          n5 = Bot
          n6 = Con(holder, [])
      }
  d4:h = Arg
  d6:x = Arg
}
exprs {
  e0 = Var(r0:h->d4:h)
  e1 = Select(e0, s0.run->d1)
  e2 = Lit(Int(1))
  e3 = App(e1, e2)
  e4 = Var(r1:h->d4:h)
  e5 = Select(e4, s1.run->d1)
  e6 = Lit(Str("x"))
  e7 = App(e5, e6)
  e8 = Tuple([e3, e7])
  e9 = Lambda(p0, e8)
  e10 = Var(r2:twice->d3:twice)
  e11 = Var(r3:holder->d0:holder)
  e12 = Lit(Int(1))
  e13 = Lambda(p1, e12)
  e14 = Record(run: e13; spread: none)
  e15 = App(e11, e14)
  e16 = App(e10, e15)
}
pats {
  p0 = Var(d4:h)
  p1 = Var(d6:x)
}

```
