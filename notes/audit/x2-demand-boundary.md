# X2 宣言 where と実需要の境界: 追加監査

対象旧 Yulang2: `d4c8bc8fc8a49173180932cd25921a2c41057354`。新specのX2との比較であり、旧実装を書き換えていない。全入力・command・stdout/stderr・所要時間・終了状態は `followup-raw.json`、再現runnerは `followup.py`。今回追加9 CLI実行。全て `--no-prelude`、5秒の外部上限。

## ソース追跡（旧 checkout 内のパス）

1. `spec/2026-06-02-role-system.md:100–124` は、impl「本体から集めた prerequisite」を照合代入後に通常のrole制約として再解決する、と記載する。宣言whereを新specのサイズ条件で拒否する説明とは異なる。
2. `crates/infer/src/module_map/mod.rs:1471–1496` は impl 直下 `WhereClause` の `WherePredicate` を `StoredRoleImplPrerequisite` に保存する。
3. `crates/infer/src/lowering/body/impl_decl.rs:183–197,272–301` はそれを `contract_advertised_prerequisites` として conformance contractへ渡す。他方、新規 `RoleImplCandidate.prerequisites` は `Vec::new()`。
4. これは偶然の読み取りではなく、`crates/infer/src/lowering/tests/case_07.rs:760–779` に `P0-A capture must not activate candidate prerequisites` というテストのassertが存在する。今回このunit test自体は実行していない。
5. 実bodyからの経路は `crates/infer/src/analysis/session/instantiate.rs:97–150` の `collect_role_impl_member_prerequisites`。schemeのrole predicatesをsimplify/projectし、finalizeした制約にquantifier外の変数があるものを集め、残余を保存するとともに `extend_role_impl_prerequisites` へ渡す。
6. `crates/infer/src/analysis/session/lifecycle.rs:280–295` は既存candidateへその残余を追加。`crates/infer/src/lowering/body/mod.rs:1620–1635` は収集済み残余をconformance contractにもhandoffする。`role_impl_conformance.rs:315–367` ではadvertisedとresidualがshadow conformance pairに別々に渡される。
7. `crates/infer/src/role_solve/mod.rs:508–531,577–654` は demand/candidate のキーをstackへ入れ、candidateのraw prerequisitesを代入して再帰解決する。同じキーの再入は抑止されるが、この断片のみから増大型の全停止性は保証できない。

## 元のX2結果をどう読むか

`impl Foo 'a`、`where (list 'a): Foo`、body `1` の宣言と `1.foo` は check=0、run=0、roots `[1]` だった。この宣言を新specの増大where禁止が拒否するはず、という点では旧実装との受理差を観測した。

ただしこれは「増大型子需要を実際に生成しても停止する」ことを検証していない。宣言advertised whereはcandidate実prerequisiteと同一ではなく、定数bodyは対応するrole methodを呼ばない。全whereが無視される、全role解決が停止する、無限再帰が解消された、といった一般化はしない。

## bodyで増大型の需要を実際に書く試験

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
1.foo
```

標準listではなく自己完結するnominal wrapperである。型の形は `'a → list 'a` と増大するが、元X2の標準list実例と全く同一とはしない。bodyが実際にwrapped receiverの `.foo` を呼び出す点を追加した試験。

| 入力 | check | dump --poly | run --print-roots |
|---|---|---|---|
| 上記から末尾 `1.foo` を除く | 0、約0.009秒 | 0、約0.010秒 | 0、約0.005秒、roots `[]` |
| 上記全文 | 5秒上限で外部中断 | 0、約0.008秒 | 5秒上限で外部中断 |
| 上記全文からwhere行だけ除く | 5秒上限で外部中断 | 0、約0.006秒 | 5秒上限で外部中断 |

全timeoutでstdout/stderrは空。`subprocess.TimeoutExpired` により外部killしたため、対象CLIが返した終了コードはない（rawでは `exit: null`、`timeout_seconds: 5`）。124を実CLIのexitとして捏造していない。

`check` は `crates/yulang/src/main.rs:584–598` で `check_poly_from_entry` を呼ぶ経路であり、少なくとも実行時だけの再帰という説明では足りない。ただしプロファイル/stacktraceは取っていないので、check内の正確な停止箇所は未確定。dump成功はcheck/run成功の代用にならない。5秒で結果がなかったことだけを確定し、非停止の数学的証明、恒久ハング、特定resolver関数が原因という断定はしない。

where無しでも同じ境界になったので、この追加観測は宣言where文だけの効果ではなくbody需要を含む試験である。decl-only成功はtop-level具体呼出成功を保証せず、元定数body成功はこの増大型呼出の反証にもならない。

## 未検証

- 5秒を越えて待てば診断/成功になるか。
- checkの停止箇所、メモリ増大、スタックの具体形。
- 標準listを使う完全同一例。
- 新Yulang3/Leanの停止定理との同一意味論対応。
- ソース参照したunit testの実行。

本追加監査によるリポジトリ変更・公開はなし。

## 追加実行の全文ログ

### grow-decl / check

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/grow-decl.yu
exit=0; elapsed=0.008733510971069336; timeout_seconds=None
STDOUT:

STDERR:

```

### grow-decl / dump

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/grow-decl.yu --poly
exit=0; elapsed=0.009526491165161133; timeout_seconds=None
STDOUT:
roots d0:list d3:Foo d5
d0:list: {value: 'a} -> list 'a = <missing>
d3:Foo mod {
  d4:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d5 mod {
  d6: 'a -> int = e5:(fn p0:d7:a -> e4:(e3:(e0:r0:list->d0:list e2:{value: e1:r1:a->d7:a}).s0.foo=>d4:"Foo.foo"))
}
detached {
  d1: list 'a -> 'a = <missing>
  d2: std::control::var::ref('a, list 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:a arg
}

STDERR:

```

### grow-decl / run

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/grow-decl.yu
exit=0; elapsed=0.004862785339355469; timeout_seconds=None
STDOUT:
run roots []

STDERR:

```

### grow-use / check

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/grow-use.yu
exit=None; elapsed=5.006412744522095; timeout_seconds=5
STDOUT:

STDERR:

```

### grow-use / dump

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/grow-use.yu --poly
exit=0; elapsed=0.00794219970703125; timeout_seconds=None
STDOUT:
roots d0:list d3:Foo d5
d0:list: {value: 'a} -> list 'a = <missing>
d3:Foo mod {
  d4:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d5 mod {
  d6: 'a -> int = e5:(fn p0:d7:a -> e4:(e3:(e0:r0:list->d0:list e2:{value: e1:r1:a->d7:a}).s0.foo=>d4:"Foo.foo"))
}
root exprs e7:(e6:1.s1.foo=>d4:"Foo.foo")
runtime roots e7:(e6:1.s1.foo=>d4:"Foo.foo")
detached {
  d1: list 'a -> 'a = <missing>
  d2: std::control::var::ref('a, list 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:a arg
}

STDERR:

```

### grow-use / run

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  where (list 'a): Foo
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/grow-use.yu
exit=None; elapsed=5.006664514541626; timeout_seconds=5
STDOUT:

STDERR:

```

### grow-nowhere / check

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-roles/grow-nowhere.yu
exit=None; elapsed=5.00630259513855; timeout_seconds=5
STDOUT:

STDERR:

```

### grow-nowhere / dump

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-roles/grow-nowhere.yu --poly
exit=0; elapsed=0.006331205368041992; timeout_seconds=None
STDOUT:
roots d0:list d3:Foo d5
d0:list: {value: 'a} -> list 'a = <missing>
d3:Foo mod {
  d4:"Foo.foo": 'a -> int where 'a: Foo = <missing>
}
my d5 mod {
  d6: 'a -> int = e5:(fn p0:d7:a -> e4:(e3:(e0:r0:list->d0:list e2:{value: e1:r1:a->d7:a}).s0.foo=>d4:"Foo.foo"))
}
root exprs e7:(e6:1.s1.foo=>d4:"Foo.foo")
runtime roots e7:(e6:1.s1.foo=>d4:"Foo.foo")
detached {
  d1: list 'a -> 'a = <missing>
  d2: std::control::var::ref('a, list 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:a arg
}

STDERR:

```

### grow-nowhere / run

```yu
struct list 'a { value: 'a }
role Foo 'a:
  our a.foo: int
impl Foo 'a:
  our a.foo = (list {value: a}).foo
1.foo
```

```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-roles/grow-nowhere.yu
exit=None; elapsed=5.006435871124268; timeout_seconds=5
STDOUT:

STDERR:

```
