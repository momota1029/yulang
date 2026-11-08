# X1〜X12 Yulang2 oracle（cycle2 subtask）

Y2 main d4c8bc8fc8a49173180932cd25921a2c41057354。no-prelude自己完結。新specの同一性を満たせない入力は一致/差と断言しない。

## Source-reading evidence

- `crates/infer/src/annotation.rs:38–63` AnnTypeにstructural record/variant無し。
- `crates/infer/src/annotation/builder.rs:181–207` build_type_baseはそれらのnodeをUnsupportedSyntaxにする。
- `crates/yulang/tests/cli.rs:1805–1828` unsupported record annotationの既存診断テスト。
- `crates/infer/src/lowering/body/impl_decl.rs:197–215,308–315` advertised prerequisitesをconformance契約へ捕捉しcandidateは空prerequisitesで初期化。body-derived依存を含む後続pipeline全体の拒否性をここだけから決めない。

## X1
通る（宣言受理） / 一致（宣言のみ）
同じopaque nominal list headとwhereの宣言はcheck0。さらに一要素wrapperをlistと名付けた近似ではbodyでDisplay子を実際に使いrun roots [1]。標準list runtimeへの同一性は主張しない。
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display (list 'a):
  where 'a: Display
  our a.display = 1
```

## X2
拒否（whereがheadより大きい; spec6.3） / 違う
増大where宣言がcheck0、呼出1.fooもrun roots [1]。lowering/body/impl_decl.rs:197–215でadvertised prerequisiteは契約へ捕捉されるが、候補は:308–315でprerequisites Vec::new()。bodyから生じないwhereを一般解決が強制したとの証拠にはならず、無限解決の停止性は試験していない。
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```

## X3
拒否（隠れた重複xを数えないとwhereは小さくない） / 実機で表せない
record型impl headはAnnType/build_type_base非対応。括弧なし原形はcheck0だがdumpで空implになり後続式も消え、意図した宣言が登録された根拠なし。拒否規則一致に数えない。
```yu
role R 'a:
  our a.r: int
impl R ({x: int, x: int}):
  where {x: int}: R
  our a.r = 1
{x: 1}.r
```

## X4
通る/保留（tail未解決） / 実機で表せない
record tailを型注釈として受ける最小例はsyntax/unsupported record type annotationで失敗。未解決R recordを正しく保存する観測に達していない。
```yu
role R 'a:
  our a.r: int
our f(x: {x: int, ..'a}) = x.r
```

## X5
拒否（payload合流後head/where同サイズ） / 実機で表せない
構造variantをimpl headに置く入力がsyntax/unresolved type tickで失敗。合流後の停止検査まで届かない。
```yu
role R 'a 'b:
  our a.r: 'b -> int
impl R 'a (:{tick (int, 'a), tick ('a, int)}):
  where 'a: R (:{tick ('a, 'a)})
  our a.r b = 1
```

## X6
拒否/曖昧（両変数にint全体を捕捉し2候補） / 実機で表せない
構造variant headがparser/lowering非対応。旧風 :tick a | :tick b も同様。nominal enumへの置換は異なるclaimなのでしない。
```yu
role R 'a:
  our a.r: int
impl R (:{tick 'a, tick 'b}):
  our a.r = 1
impl R (:{tick int}):
  our a.r = 2
(:tick 1).r
```

## X7
拒否（隠れたfieldのaで関連型が決まらない） / 実機で表せない
record型impl headのsyntax/unresolved xで失敗。関連型決定性の拒否ではない。
```yu
role R 'a:
  type value
  our a.r: value
impl R ({x: int, x: 'a}):
  type value = 'a
  our a.r = a.x
```

## X8
通る（list内のμを変数捕捉するだけ） / 実機で表せない/未確認
check0だがdumpでloop:any->{next:never}。求める構造再帰μを生成した証拠がなく、さらにopaque listとliteralのstd::data::list::listは別名。K2受理の一致としては採用しない。
```yu
type list 'a
role Len 'a:
  our a.len: int
impl Len (list 'a):
  our a.len = 0
our loop x = {next: loop x}
our result() = [loop 1].len
```

## X9
拒否（Show μへ到達; spec6.3 K2） / 実機で表せない/未確認
check0だがX8と同じくμ未成立、unused advertised whereもbodyで使用なし。K2差と断言しない。
```yu
type list 'a
role Show 'a:
  our a.show: int
impl Show (list 'a):
  where 'a: Show
  our a.show = 0
our loop x = {next: loop x}
our result() = [loop 1].show
```

## X10
拒否（μのconstructorをinspectする） / 実機で表せない
record head入力は空impl化し後続loop/resultがdumpにない。正しい型headを生成できずK2まで届かない。
```yu
role Check 'a:
  our a.check: int
impl Check {box: {tick: 'a}}:
  where {box: 'a}: Check
  our a.check = 0
our loop x = {tick: loop x}
our result() = {box: loop 0}.check
```

## X11
拒否（unsafe候補が曖昧性/選択より先） / 実機で表せない
record headがsyntax/unresolved boxで失敗。loopもμ未成立。拒否の理由がK2ではないため一致ではない。
```yu
role Check 'a:
  our a.check: int
impl Check ({box: 'a}):
  our a.check = 0
impl Check ({box: {next: 'b}}):
  our a.check = 1
our loop x = {next: loop x}
our result() = {box: loop 0}.check
```

## X12
通る（名前付き再帰enum tree） / 一致
enum tree、Show treeを定義してleaf値へ適用。check0/run0、--polyでtree->int implが確認できる。--print-roots付き再試験でrun roots [1]を確認。
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```

# 実行原文（探索失敗も全て保存）

## 1. X1
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display (list 'a):
  where 'a: Display
  our a.display = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X1.yu
```
exit=0; elapsed=0.004148s
stdout:
```text

```
stderr:
```text

```

## 2. X1
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display (list 'a):
  where 'a: Display
  our a.display = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X1.yu --poly
```
exit=0; elapsed=0.003405s
stdout:
```text
roots d0:Display d2
d0:Display mod {
  d1:"Display.display": 'a -> int where 'a: Display = <missing>
}
my d2 mod {
  d3: list 'a -> int = e1:(fn p0:d4:a -> e0:1)
}
detached {
  d4:a arg
}

```
stderr:
```text

```

## 3. X2
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X2.yu
```
exit=0; elapsed=0.003038s
stdout:
```text

```
stderr:
```text

```

## 4. X2
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X2.yu --poly
```
exit=0; elapsed=0.002964s
stdout:
```text
roots d0:Foo d2
d0:Foo mod {
  d1:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d2 mod {
  d3: 'a -> int = e1:(fn p0:d4:a -> e0:1)
}
detached {
  d4:a arg
}

```
stderr:
```text

```

## 5. X3
```yu
role R 'a:
  our a.r: int
impl R {x: int, x: int}:
  where {x: int}: R
  our a.r = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X3.yu
```
exit=0; elapsed=0.003121s
stdout:
```text

```
stderr:
```text

```

## 6. X3
```yu
role R 'a:
  our a.r: int
impl R {x: int, x: int}:
  where {x: int}: R
  our a.r = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X3.yu --poly
```
exit=0; elapsed=0.003945s
stdout:
```text
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
}

```
stderr:
```text

```

## 7. X4
```yu
role R 'a:
  our a.r: int
our f(x: {x: int, ..'a}) = x.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X4.yu
```
exit=1; elapsed=0.002497s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 19
    3 | our f(x: {x: int, ..'a}) = x.r
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 20
    3 | our f(x: {x: int, ..'a}) = x.r
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 21
    3 | our f(x: {x: int, ..'a}) = x.r
      |                     ^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 23
    3 | our f(x: {x: int, ..'a}) = x.r
      |                       ^
  error [yulang.unsupported-type-syntax]: f: unsupported type annotation syntax: record type annotation
    --> line 3, column 10
    3 | our f(x: {x: int, ..'a}) = x.r
      |          ^^^^^^^^^^^^^
    hint: use a supported type annotation form and keep effect rows in effect position

```
stderr:
```text

```

## 8. X4
```yu
role R 'a:
  our a.r: int
our f(x: {x: int, ..'a}) = x.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X4.yu --poly
```
exit=0; elapsed=0.003665s
stdout:
```text
roots d0:R d2:f
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
d2:f: never = <missing>

```
stderr:
```text
error: unsupported type annotation syntax: record type annotation

```

## 9. X5
```yu
role R 'a 'b:
  our a.r: 'b -> int
impl R 'a (:{tick (int, 'a), tick ('a, int)}):
  where 'a: R (:{tick ('a, 'a)})
  our a.r b = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X5.yu
```
exit=1; elapsed=0.003574s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 12
    3 | impl R 'a (:{tick (int, 'a), tick ('a, int)}):
      |            ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 13
    3 | impl R 'a (:{tick (int, 'a), tick ('a, int)}):
      |             ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 44
    3 | impl R 'a (:{tick (int, 'a), tick ('a, int)}):
      |                                            ^
  error [yulang.unresolved-type]: d2: unresolved type name: tick
    hint: define type `tick` before this annotation, or import it

```
stderr:
```text

```

## 10. X5
```yu
role R 'a 'b:
  our a.r: 'b -> int
impl R 'a (:{tick (int, 'a), tick ('a, int)}):
  where 'a: R (:{tick ('a, 'a)})
  our a.r b = 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X5.yu --poly
```
exit=0; elapsed=0.007549s
stdout:
```text
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> 'b -> int where 'a: R 'b = <missing>
}
my d2 mod {
  d3 = <missing>
}

```
stderr:
```text
error: unresolved type name: tick

```

## 11. X6
```yu
role R 'a:
  our a.r: int
impl R (:{tick 'a, tick 'b}):
  our a.r = 1
impl R (:{tick int}):
  our a.r = 2
(:tick 1).r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X6.yu
```
exit=1; elapsed=0.003944s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 9
    3 | impl R (:{tick 'a, tick 'b}):
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 10
    3 | impl R (:{tick 'a, tick 'b}):
      |          ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 27
    3 | impl R (:{tick 'a, tick 'b}):
      |                           ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 9
    5 | impl R (:{tick int}):
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 10
    5 | impl R (:{tick int}):
      |          ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 | impl R (:{tick int}):
      |                   ^
  error [yulang.unresolved-type]: d2: unresolved type name: tick
    hint: define type `tick` before this annotation, or import it
  error [yulang.unresolved-type]: d4: unresolved type name: tick
    hint: define type `tick` before this annotation, or import it

```
stderr:
```text

```

## 12. X6
```yu
role R 'a:
  our a.r: int
impl R (:{tick 'a, tick 'b}):
  our a.r = 1
impl R (:{tick int}):
  our a.r = 2
(:tick 1).r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X6.yu --poly
```
exit=0; elapsed=0.003843s
stdout:
```text
roots d0:R d2 d4
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3 = <missing>
}
my d4 mod {
  d5 = <missing>
}
root exprs e2:(e1::tick(e0:1).s0.r=>d1:"R.r")
runtime roots e2:(e1::tick(e0:1).s0.r=>d1:"R.r")

```
stderr:
```text
error: unresolved type name: tick
error: unresolved type name: tick

```

## 13. X7
```yu
role R 'a:
  type value
  our a.r: value
impl R ({x: int, x: 'a}):
  type value = 'a
  our a.r = a.x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X7.yu
```
exit=1; elapsed=0.003026s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 9
    4 | impl R ({x: int, x: 'a}):
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 11
    4 | impl R ({x: int, x: 'a}):
      |           ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 19
    4 | impl R ({x: int, x: 'a}):
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 23
    4 | impl R ({x: int, x: 'a}):
      |                       ^
  error [yulang.unresolved-type]: d2: unresolved type name: x
    hint: define type `x` before this annotation, or import it

```
stderr:
```text

```

## 14. X7
```yu
role R 'a:
  type value
  our a.r: value
impl R ({x: int, x: 'a}):
  type value = 'a
  our a.r = a.x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X7.yu --poly
```
exit=0; elapsed=0.002718s
stdout:
```text
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> 'b where 'a: R(value = 'b) = <missing>
}
my d2 mod {
  d3 = <missing>
}

```
stderr:
```text
error: unresolved type name: x

```

## 15. X8
```yu
type list 'a
role Len 'a:
  our a.len: int
impl Len (list 'a):
  our a.len = 0
our loop x = {next: loop x}
our result() = [loop 1].len
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X8.yu
```
exit=0; elapsed=0.005350s
stdout:
```text

```
stderr:
```text

```

## 16. X8
```yu
type list 'a
role Len 'a:
  our a.len: int
impl Len (list 'a):
  our a.len = 0
our loop x = {next: loop x}
our result() = [loop 1].len
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X8.yu --poly
```
exit=0; elapsed=0.006112s
stdout:
```text
roots d0:Len d2 d4:loop d5:result
d0:Len mod {
  d1:"Len.len": 'a -> int where 'a: Len = <missing>
}
my d2 mod {
  d3: list 'a -> int = e1:(fn p0:d6:a -> e0:0)
}
d4:loop: any -> {next: never} = e6:(fn p1:d7:x -> e5:{next: e4:(e2:r0:loop->d4:loop e3:r1:x->d7:x)})
d5:result: () -> int = e13:(fn p2:() -> e12:(e11:(e10:builtin_op::list_singleton e9:(e7:r2:loop->d4:loop e8:1)).s0.len=>d1:"Len.len"))
detached {
  d6:a arg
  d7:x arg
}

```
stderr:
```text

```

## 17. X9
```yu
type list 'a
role Show 'a:
  our a.show: int
impl Show (list 'a):
  where 'a: Show
  our a.show = 0
our loop x = {next: loop x}
our result() = [loop 1].show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X9.yu
```
exit=0; elapsed=0.005304s
stdout:
```text

```
stderr:
```text

```

## 18. X9
```yu
type list 'a
role Show 'a:
  our a.show: int
impl Show (list 'a):
  where 'a: Show
  our a.show = 0
our loop x = {next: loop x}
our result() = [loop 1].show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X9.yu --poly
```
exit=0; elapsed=0.006227s
stdout:
```text
roots d0:Show d2 d4:loop d5:result
d0:Show mod {
  d1:"Show.show": 'a -> int where 'a: Show = <missing>
}
my d2 mod {
  d3: list 'a -> int = e1:(fn p0:d6:a -> e0:0)
}
d4:loop: any -> {next: never} = e6:(fn p1:d7:x -> e5:{next: e4:(e2:r0:loop->d4:loop e3:r1:x->d7:x)})
d5:result: () -> int = e13:(fn p2:() -> e12:(e11:(e10:builtin_op::list_singleton e9:(e7:r2:loop->d4:loop e8:1)).s0.show=>d1:"Show.show"))
detached {
  d6:a arg
  d7:x arg
}

```
stderr:
```text

```

## 19. X10
```yu
role Check 'a:
  our a.check: int
impl Check {box: {tick: 'a}}:
  where {box: 'a}: Check
  our a.check = 0
our loop x = {tick: loop x}
our result() = {box: loop 0}.check
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X10.yu
```
exit=0; elapsed=0.002697s
stdout:
```text

```
stderr:
```text

```

## 20. X10
```yu
role Check 'a:
  our a.check: int
impl Check {box: {tick: 'a}}:
  where {box: 'a}: Check
  our a.check = 0
our loop x = {tick: loop x}
our result() = {box: loop 0}.check
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X10.yu --poly
```
exit=0; elapsed=0.003316s
stdout:
```text
roots d0:Check d2
d0:Check mod {
  d1:"Check.check": 'a -> int where 'a: Check = <missing>
}
my d2 mod {
}

```
stderr:
```text

```

## 21. X11
```yu
role Check 'a:
  our a.check: int
impl Check ({box: 'a}):
  our a.check = 0
impl Check ({box: {next: 'b}}):
  our a.check = 1
our loop x = {next: loop x}
our result() = {box: loop 0}.check
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X11.yu
```
exit=1; elapsed=0.004318s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 13
    3 | impl Check ({box: 'a}):
      |             ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 17
    3 | impl Check ({box: 'a}):
      |                 ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 21
    3 | impl Check ({box: 'a}):
      |                     ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 13
    5 | impl Check ({box: {next: 'b}}):
      |             ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 17
    5 | impl Check ({box: {next: 'b}}):
      |                 ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 | impl Check ({box: {next: 'b}}):
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 24
    5 | impl Check ({box: {next: 'b}}):
      |                        ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 28
    5 | impl Check ({box: {next: 'b}}):
      |                            ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 29
    5 | impl Check ({box: {next: 'b}}):
      |                             ^
  error [yulang.unresolved-type]: d2: unresolved type name: box
    hint: define type `box` before this annotation, or import it
  error [yulang.unresolved-type]: d4: unresolved type name: box
    hint: define type `box` before this annotation, or import it

```
stderr:
```text

```

## 22. X11
```yu
role Check 'a:
  our a.check: int
impl Check ({box: 'a}):
  our a.check = 0
impl Check ({box: {next: 'b}}):
  our a.check = 1
our loop x = {next: loop x}
our result() = {box: loop 0}.check
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X11.yu --poly
```
exit=0; elapsed=0.005797s
stdout:
```text
roots d0:Check d2 d4 d6:loop d7:result
d0:Check mod {
  d1:"Check.check": 'a -> int where 'a: Check = <missing>
}
my d2 mod {
  d3 = <missing>
}
my d4 mod {
  d5 = <missing>
}
d6:loop: any -> {next: never} = e4:(fn p0:d8:x -> e3:{next: e2:(e0:r0:loop->d6:loop e1:r1:x->d8:x)})
d7:result: () -> int where {box: {next: never}}: Check = e10:(fn p1:() -> e9:(e8:{box: e7:(e5:r2:loop->d6:loop e6:0)}.s0.check=>d1:"Check.check"))
detached {
  d8:x arg
}

```
stderr:
```text
error: unresolved type name: box
error: unresolved type name: box

```

## 23. X12
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X12.yu
```
exit=0; elapsed=0.004155s
stdout:
```text

```
stderr:
```text

```

## 24. X12
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X12.yu --poly
```
exit=0; elapsed=0.003957s
stdout:
```text
roots d0:tree d3:Show d5
d0:tree mod {
  d1:"tree.leaf": int -> tree = <missing>
  d2:"tree.branch": tree -> tree -> tree = <missing>
}
d3:Show mod {
  d4:"Show.show": 'a -> int where 'a: Show = <missing>
}
my d5 mod {
  d6: tree -> int = e1:(fn p0:d7:a -> e0:1)
}
root exprs e5:(e4:(e2:r0:"tree::leaf"->d1:"tree.leaf" e3:1).s0.show=>d4:"Show.show")
runtime roots e5:(e4:(e2:r0:"tree::leaf"->d1:"tree.leaf" e3:1).s0.show=>d4:"Show.show")
detached {
  d7:a arg
}

```
stderr:
```text

```

## 25. X1-use
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
[1].display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X1-use.yu
```
exit=1; elapsed=0.005862s
stdout:
```text
diagnostics:
  error [yulang.unresolved-method]: display: no role implementation satisfies this method call for receiver std::data::list::list(int)
    --> line 9, column 5
    9 | [1].display
      |     ^^^^^^^
    hint: add or import an impl for the receiver type, or call a method supported by that value

```
stderr:
```text

```

## 26. X1-use
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
[1].display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X1-use.yu --poly
```
exit=0; elapsed=0.005134s
stdout:
```text
roots d0:Display d2 d4
d0:Display mod {
  d1:"Display.display": 'a -> int where 'a: Display = <missing>
}
my d2 mod {
  d3: int -> int = e1:(fn p0:d6:a -> e0:1)
}
my d4 mod {
  d5: list 'a -> int = e3:(fn p1:d7:a -> e2:2)
}
root exprs e7:(e6:(e5:builtin_op::list_singleton e4:1).s0.display=>d1:"Display.display")
runtime roots e7:(e6:(e5:builtin_op::list_singleton e4:1).s0.display=>d1:"Display.display")
detached {
  d6:a arg
  d7:a arg
}

```
stderr:
```text

```

## 27. X1-use
```yu
type list 'a
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
[1].display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-roles/X1-use.yu
```
exit=1; elapsed=0.005895s
stdout:
```text

```
stderr:
```text
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 9, column 5
    9 | [1].display
      |     ^^^^^^^
  detail: no role implementation satisfies this method call for receiver std::data::list::list(int)
  hint: add or import an impl for the receiver type, or call a method supported by that value

```

## 28. X2-use
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X2-use.yu
```
exit=0; elapsed=0.003396s
stdout:
```text

```
stderr:
```text

```

## 29. X2-use
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X2-use.yu --poly
```
exit=0; elapsed=0.003038s
stdout:
```text
roots d0:Foo d2
d0:Foo mod {
  d1:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d2 mod {
  d3: 'a -> int = e1:(fn p0:d4:a -> e0:1)
}
root exprs e3:(e2:1.s0.foo=>d1:"Foo.foo")
runtime roots e3:(e2:1.s0.foo=>d1:"Foo.foo")
detached {
  d4:a arg
}

```
stderr:
```text

```

## 30. X3-colon
```yu
role R 'a:
  our a.r: int
impl {x: int, x: int}: R:
  where {x: int}: R
  our a.r = 1
{x: 1}.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X3-colon.yu
```
exit=1; elapsed=0.002270s
stdout:
```text
diagnostics:
  error [yulang.unsupported-syntax]: d2: unsupported expression syntax: impl declaration
    hint: rewrite this form using supported expression syntax

```
stderr:
```text

```

## 31. X3-colon
```yu
role R 'a:
  our a.r: int
impl {x: int, x: int}: R:
  where {x: int}: R
  our a.r = 1
{x: 1}.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X3-colon.yu --poly
```
exit=0; elapsed=0.003820s
stdout:
```text
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
}

```
stderr:
```text
error: unsupported expression syntax: impl declaration

```

## 32. X3-paren
```yu
role R 'a:
  our a.r: int
impl R ({x: int, x: int}):
  where {x: int}: R
  our a.r = 1
{x: 1}.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X3-paren.yu
```
exit=1; elapsed=0.003263s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 9
    3 | impl R ({x: int, x: int}):
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 11
    3 | impl R ({x: int, x: int}):
      |           ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 19
    3 | impl R ({x: int, x: int}):
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 24
    3 | impl R ({x: int, x: int}):
      |                        ^
  error [yulang.unresolved-type]: d2: unresolved type name: x
    hint: define type `x` before this annotation, or import it

```
stderr:
```text

```

## 33. X3-paren
```yu
role R 'a:
  our a.r: int
impl R ({x: int, x: int}):
  where {x: int}: R
  our a.r = 1
{x: 1}.r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X3-paren.yu --poly
```
exit=0; elapsed=0.003705s
stdout:
```text
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3 = <missing>
}
root exprs e2:(e1:{x: e0:1}.s0.r=>d1:"R.r")
runtime roots e2:(e1:{x: e0:1}.s0.r=>d1:"R.r")

```
stderr:
```text
error: unresolved type name: x

```

## 34. X6-oldvariant
```yu
role R 'a:
  our a.r: int
impl R (:tick 'a | :tick 'b):
  our a.r = 1
impl R (:tick int):
  our a.r = 2
(:tick 1).r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X6-oldvariant.yu
```
exit=1; elapsed=0.003108s
stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 9
    3 | impl R (:tick 'a | :tick 'b):
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 18
    3 | impl R (:tick 'a | :tick 'b):
      |                  ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 20
    3 | impl R (:tick 'a | :tick 'b):
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 9
    5 | impl R (:tick int):
      |         ^
  error [yulang.unresolved-type]: d2: unresolved type name: tick
    hint: define type `tick` before this annotation, or import it
  error [yulang.unresolved-type]: d4: unresolved type name: tick
    hint: define type `tick` before this annotation, or import it

```
stderr:
```text

```

## 35. X6-oldvariant
```yu
role R 'a:
  our a.r: int
impl R (:tick 'a | :tick 'b):
  our a.r = 1
impl R (:tick int):
  our a.r = 2
(:tick 1).r
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X6-oldvariant.yu --poly
```
exit=0; elapsed=0.003412s
stdout:
```text
roots d0:R d2 d4
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3 = <missing>
}
my d4 mod {
  d5 = <missing>
}
root exprs e2:(e1::tick(e0:1).s0.r=>d1:"R.r")
runtime roots e2:(e1::tick(e0:1).s0.r=>d1:"R.r")

```
stderr:
```text
error: unresolved type name: tick
error: unresolved type name: tick

```

## 36. knot-record
```yu
my knot = {next: knot}
our result() = knot
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/knot-record.yu
```
exit=0; elapsed=0.003041s
stdout:
```text

```
stderr:
```text

```

## 37. knot-record
```yu
my knot = {next: knot}
our result() = knot
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/knot-record.yu --poly
```
exit=0; elapsed=0.003214s
stdout:
```text
roots d0:knot d1:result
my d0:knot: {next: never} = e1:{next: e0:r0:knot->d0:knot}
d1:result: () -> {next: never} = e3:(fn p0:() -> e2:r1:knot->d0:knot)

```
stderr:
```text

```

## 38. knot-nominal
```yu
struct loop 'a { next: 'a }
my knot = loop {next: knot}
our result() = knot
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/knot-nominal.yu
```
exit=0; elapsed=0.004958s
stdout:
```text

```
stderr:
```text

```

## 39. knot-nominal
```yu
struct loop 'a { next: 'a }
my knot = loop {next: knot}
our result() = knot
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/knot-nominal.yu --poly
```
exit=0; elapsed=0.006118s
stdout:
```text
roots d0:loop d3:knot d4:result
d0:loop: {next: 'a} -> loop 'a = <missing>
my d3:knot: loop 'a = e3:(e0:r0:loop->d0:loop e2:{next: e1:r1:knot->d3:knot})
d4:result: () -> loop 'a = e5:(fn p0:() -> e4:r2:knot->d3:knot)
runtime roots d3:knot
detached {
  d1: loop 'a -> 'a = <missing>
  d2: std::control::var::ref('a, loop 'b) -> std::control::var::ref 'a 'b = <missing>
}

```
stderr:
```text

```

## 40. X12-run
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X12-run.yu
```
exit=0; elapsed=0.004757s
stdout:
```text

```
stderr:
```text

```

## 41. X12-run
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X12-run.yu --poly
```
exit=0; elapsed=0.005455s
stdout:
```text
roots d0:tree d3:Show d5
d0:tree mod {
  d1:"tree.leaf": int -> tree = <missing>
  d2:"tree.branch": tree -> tree -> tree = <missing>
}
d3:Show mod {
  d4:"Show.show": 'a -> int where 'a: Show = <missing>
}
my d5 mod {
  d6: tree -> int = e1:(fn p0:d7:a -> e0:1)
}
root exprs e5:(e4:(e2:r0:"tree::leaf"->d1:"tree.leaf" e3:1).s0.show=>d4:"Show.show")
runtime roots e5:(e4:(e2:r0:"tree::leaf"->d1:"tree.leaf" e3:1).s0.show=>d4:"Show.show")
detached {
  d7:a arg
}

```
stderr:
```text

```

## 42. X12-run
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-roles/X12-run.yu
```
exit=0; elapsed=0.002874s
stdout:
```text

```
stderr:
```text

```

## 43. loop-selfreturn
```yu
our loop x = loop
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/loop-selfreturn.yu
```
exit=0; elapsed=0.004778s
stdout:
```text

```
stderr:
```text

```

## 44. loop-selfreturn
```yu
our loop x = loop
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/loop-selfreturn.yu --poly
```
exit=0; elapsed=0.004505s
stdout:
```text
roots d0:loop d1:result
d0:loop: any -> any -> never = e1:(fn p0:d2:x -> e0:r0:loop->d0:loop)
d1:result: () -> any -> never = e5:(fn p1:() -> e4:(e2:r1:loop->d0:loop e3:1))
detached {
  d2:x arg
}

```
stderr:
```text

```

## 45. loop-idbranch
```yu
our loop x = if true: x else: {next: loop x}
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/loop-idbranch.yu
```
exit=1; elapsed=0.003201s
stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: loop: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our loop x = if true: x else: {next: loop x}
      |     ^^^^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it

```
stderr:
```text

```

## 46. loop-idbranch
```yu
our loop x = if true: x else: {next: loop x}
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/loop-idbranch.yu --poly
```
exit=0; elapsed=0.003870s
stdout:
```text
roots d0:loop d1:result
d0:loop: never = <missing>
d1:result: () -> never = e4:(fn p1:() -> e3:(e1:r0:loop->d0:loop e2:1))
detached {
  d2:x arg
}

```
stderr:
```text
error: unresolved value name: std::control::junction::junction::junction

```

## 47. loop-tuple
```yu
our loop x = (x, loop x)
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/loop-tuple.yu
```
exit=0; elapsed=0.004143s
stdout:
```text

```
stderr:
```text

```

## 48. loop-tuple
```yu
our loop x = (x, loop x)
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/loop-tuple.yu --poly
```
exit=0; elapsed=0.004524s
stdout:
```text
roots d0:loop d1:result
d0:loop: 'a -> ('a, never) = e5:(fn p0:d2:x -> e4:(e0:r0:x->d2:x, e3:(e1:r1:loop->d0:loop e2:r2:x->d2:x)))
d1:result: () -> (int, never) = e9:(fn p1:() -> e8:(e6:r3:loop->d0:loop e7:1))
detached {
  d2:x arg
}

```
stderr:
```text

```

## 49. loop-selfrecord
```yu
our loop x = {next: loop}
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/loop-selfrecord.yu
```
exit=0; elapsed=0.003241s
stdout:
```text

```
stderr:
```text

```

## 50. loop-selfrecord
```yu
our loop x = {next: loop}
our result() = loop 1
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/loop-selfrecord.yu --poly
```
exit=0; elapsed=0.004184s
stdout:
```text
roots d0:loop d1:result
d0:loop: any -> {next: any -> never} = e2:(fn p0:d2:x -> e1:{next: e0:r0:loop->d0:loop})
d1:result: () -> {next: any -> never} = e6:(fn p1:() -> e5:(e3:r1:loop->d0:loop e4:1))
detached {
  d2:x arg
}

```
stderr:
```text

```

## 51. X1-custom-list
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X1-custom-list.yu
```
exit=0; elapsed=0.005507s
stdout:
```text

```
stderr:
```text

```

## 52. X1-custom-list
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X1-custom-list.yu --poly
```
exit=0; elapsed=0.004998s
stdout:
```text
roots d0:list d3:Display d5 d7
d0:list: {value: 'a} -> list 'a = <missing>
d3:Display mod {
  d4:"Display.display": 'a -> int where 'a: Display = <missing>
}
my d5 mod {
  d6: int -> int = e1:(fn p0:d9:a -> e0:1)
}
my d7 mod {
  d8: list 'a -> int = e3:(fn p1:d10:a -> e2:2)
}
root exprs e8:(e7:(e4:r0:list->d0:list e6:{value: e5:1}).s0.display=>d4:"Display.display")
runtime roots e8:(e7:(e4:r0:list->d0:list e6:{value: e5:1}).s0.display=>d4:"Display.display")
detached {
  d1: list 'a -> 'a = <missing>
  d2: std::control::var::ref('a, list 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:a arg
  d10:a arg
}

```
stderr:
```text

```

## 53. X1-custom-list
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = 2
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/X1-custom-list.yu
```
exit=0; elapsed=0.003096s
stdout:
```text
run roots [2]

```
stderr:
```text

```

## 54. X1-actual-demand
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = a.value.display
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X1-actual-demand.yu
```
exit=0; elapsed=0.006256s
stdout:
```text

```
stderr:
```text

```

## 55. X1-actual-demand
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = a.value.display
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X1-actual-demand.yu --poly
```
exit=0; elapsed=0.008760s
stdout:
```text
roots d0:list d3:Display d5 d7
d0:list: {value: 'a} -> list 'a = <missing>
d3:Display mod {
  d4:"Display.display": 'a -> int where 'a: Display = <missing>
}
my d5 mod {
  d6: int -> int = e1:(fn p0:d9:a -> e0:1)
}
my d7 mod {
  d8: list 'a -> int where 'a: Display = e5:(fn p1:d10:a -> e4:(e3:(e2:r0:a->d10:a.s0.value->d1).s1.display=>d4:"Display.display"))
}
root exprs e10:(e9:(e6:r1:list->d0:list e8:{value: e7:1}).s2.display=>d4:"Display.display")
runtime roots e10:(e9:(e6:r1:list->d0:list e8:{value: e7:1}).s2.display=>d4:"Display.display")
detached {
  d1: list 'a -> 'a = <missing>
  d2: std::control::var::ref('a, list 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:a arg
  d10:a arg
}

```
stderr:
```text

```

## 56. X1-actual-demand
```yu
struct list 'a { value: 'a }
role Display 'a:
  our a.display: int
impl Display int:
  our a.display = 1
impl Display (list 'a):
  where 'a: Display
  our a.display = a.value.display
(list {value: 1}).display
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/X1-actual-demand.yu
```
exit=0; elapsed=0.004301s
stdout:
```text
run roots [1]

```
stderr:
```text

```

## 57. X2-same
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/X2-same.yu
```
exit=0; elapsed=0.005150s
stdout:
```text

```
stderr:
```text

```

## 58. X2-same
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/X2-same.yu --poly
```
exit=0; elapsed=0.004640s
stdout:
```text
roots d0:Foo d2
d0:Foo mod {
  d1:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d2 mod {
  d3: 'a -> int = e1:(fn p0:d4:a -> e0:1)
}
root exprs e3:(e2:1.s0.foo=>d1:"Foo.foo")
runtime roots e3:(e2:1.s0.foo=>d1:"Foo.foo")
detached {
  d4:a arg
}

```
stderr:
```text

```

## 59. X2-same
```yu
type list 'a
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = 1
1.foo
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/X2-same.yu
```
exit=0; elapsed=0.003652s
stdout:
```text
run roots [1]

```
stderr:
```text

```

## 60. X12-run
```yu
enum tree:
  leaf int
  branch (tree, tree)
role Show 'a:
  our a.show: int
impl Show tree:
  our a.show = 1
(tree::leaf 1).show
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/X12-run.yu
```
exit=0; elapsed=0.003256s
stdout:
```text
run roots [1]

```
stderr:
```text

```
