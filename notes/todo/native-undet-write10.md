読んだよ〜。
これはかなり良い報告で、**原因はもう「謎の runtime bug」ではなく、かなり限定された lowering の責務漏れ** に見えるねぇ。

結論から言うと、次は **Phase F.5 step 5 を実装するべき** だと思う。
ただし、`eval_cps_module` 側で root thunk を無条件に force するのではなく、**lowering 時に「この return は non-thunk を要求している」と分かる場所だけ `ForceThunk` を挿む** のが安全だよ〜。

---

# 状況整理

報告書の最重要点はこれだねぇ。

```text
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}

case work().once:
    nil -> 0
    just v -> v
```

これが CPS eval の段階で、

```text
Thunk(owner: work__mono0, entry: cont(1), handlers: [...once arms...])
```

を root に返してしまい、`ExpectedPlainValue` で落ちている。つまり **`work()` の effectful body が thunk に包まれたまま、最終的な `int` 文脈まで漏れている** ということだねぇ。報告でも、ApplyClosure / DirectCall result forcing は入れたが、`lower_root` / `lower_binding` / lambda body return は未実装と書かれている。

一方、直前の大きな修正では `MakeRecursiveClosure` の self-reference は直っていて、`std::undet.once` の基本 scalar-unwrapped regression は通っている。`force_if_non_thunk_demand` も ApplyClosure / DirectCall results には入っている状態だねぇ。

だから今は、

```text
call/apply の結果 forcing はある
function/root/lambda return の forcing がない
```

が一番疑わしい。

---

# 次にやるべきこと

## 1. Phase F.5 step 5 を実装する

これはやるべき。
ただし、名前を少し厳密にしておくと安全。

今ある `force_if_non_thunk_demand` は便利だけど、over-forcing が怖いなら、return 用にはもう少し保守的な helper にする。

```rust
fn force_if_definitely_value_demand(
    &mut self,
    value: CpsValueId,
    expected_ty: &runtime::Type,
) -> CpsValueId {
    if !definitely_demands_forced_value(expected_ty) {
        return value;
    }

    let forced = self.fresh_value();
    self.current.stmts.push(CpsStmt::ForceThunk {
        dest: forced,
        thunk: value,
    });
    forced
}
```

`definitely_demands_forced_value` は、最初は保守的でいい。

```rust
fn definitely_demands_forced_value(ty: &runtime::Type) -> bool {
    match ty {
        runtime::Type::Thunk { .. } => false,

        // 関数・未知型・型変数などは first-class value として流す可能性があるので
        // ここでは無理に force しない方が安全。
        runtime::Type::Fun { .. } => false,
        runtime::Type::Unknown => false,

        // 実際の Type enum に合わせて TypeVar / Raw / Dynamic などがあれば false 側。
        // _ を true にするより、具体型だけ true にする方が安全。
        runtime::Type::Int
        | runtime::Type::Bool
        | runtime::Type::Unit
        | runtime::Type::Float
        | runtime::Type::String
        | runtime::Type::List(_)
        | runtime::Type::Tuple(_)
        | runtime::Type::Record(_)
        | runtime::Type::Variant(_) => true,

        _ => false,
    }
}
```

実際の `runtime::Type` の variant 名は合わせてねぇ。
ポイントは、**Unknown を non-thunk 扱いして雑に force しない** こと。

ただ、既存の `force_if_non_thunk_demand` がすでに広めに使われていてテストが通っているなら、まずはそれを return にも使って、後で guard を厳しくするでもいい。今回の failing case は `work(): int` や root `int` なので、型はかなり concrete なはず。

---

## 2. どこに force を入れるか

優先順はこれ。

### A. function / binding body の return

`lower_binding` か `FunctionLowerer::lower_root` の最後で、body result を return する直前。

擬似コード:

```rust
let value = self.lower_expr(body)?;
let value = self.force_if_non_thunk_demand(value, &body.ty);
self.terminate(CpsTerminator::Return(value));
self.finish_current();
```

ここが一番大事。
`work__mono0` が `int` を返すなら、ここで thunk leak を潰せる。

### B. root expression の return

root も同じ。

```rust
let value = self.lower_expr(root_expr)?;
let value = self.force_if_non_thunk_demand(value, &root_expr.ty);
Return(value)
```

ただし root で無条件 force ではなく、**lowering で root expr type を見て force** する。
これは evaluator 側で root thunk を全部 force するよりずっと安全。

### C. lambda / recursive lambda body の return

`lower_lambda` / `lower_recursive_lambda` の末尾にも入れる。

```rust
let value = self.lower_expr(body)?;
let value = self.force_if_non_thunk_demand(value, &body.ty);
Return(value)
```

`MakeRecursiveClosure` の self-reference はもう直っているけど、recursive closure body が thunk を返すケースは今後も出るので、ここも入れておくと安全だと思う。

### D. handler value arm は後回しでいい

`finish_handled_value` / `finish_resumed_handled_value` に入れるかは慎重に。
まずは root / binding / lambda return だけで `work().once` が直るか確認するのがいい。

---

# 3. 今回の failing case に対する期待

修正後、`work__mono0` の return 直前にこうなるのが期待。

```text
MakeThunk V...
ForceThunk V...   // work(): int なので return 前に force
Return V...
```

または root 側で、

```text
DirectCall work__mono0
ForceThunk
...
Return Plain(...)
```

になる。

ただし、`work()` が `.once` の引数として thunk を要求されている文脈なら、force してはいけない。
そこは **expected type** が大事。

報告の failing case は最終 root が `int` なので、最終的にはどこかで force されるべきだよ〜。

---

# 4. Hypothesis C の切り分けは必要か？

やってもいいけど、**Phase F.5 step 5 の後でいい**。

報告の仮説 C、つまり guard / if-else が増えることで thunk path が外へ漏れる、という見立てはかなりありそう。
でも、今は修正すべき場所が明確だから、先に return forcing を入れた方が早い。

修正後まだ落ちるなら、次の小さいテストで切る。

## effect なし if

```yulang
my work(): int = {
    my n = 1
    if n > 0:
        n
    else:
        0
}

work()
```

これは native CPS で普通に通るべき。

## effect あり guard なし

これは報告上すでに通っている。

```yulang
my work(): int = each [1, 2, 3]

case work().once:
    nil -> 0
    just x -> x
```

## effect あり guard あり

現在 failing。

```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}
case work().once:
    nil -> 0
    just x -> x
```

この差分で、`guard` が thunk-return path を作っているか見ればいいねぇ。

---

# 5. recursive closure regression の書き方

`sum_down` が `ResidualPolymorphicBinding` で落ちるなら、それは regression として不向き。報告どおり、top-level direct recursion は monomorphizer / polymorphism 側の別問題に引っかかっている。

`MakeRecursiveClosure` を確実に踏みたいなら、`with: our loop` 型の local recursive function が良いと思う。

たとえば、構文が合うならこう。

```rust
#[test]
fn compares_local_recursive_loop_self_reference_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
loop 3 with:
    our loop(n: int): int = if n == 0:
        0
    else:
        1 + loop (n - 1)
"#).expect("local recursive loop self-reference");
    });
}
```

もし `loop 3 with:` の形が合わなければ、`std::undet.once` に出てくる形を真似て、

```yulang
loop 3 0 with:
    our loop(n: int, acc: int): int = if n == 0:
        acc
    else:
        loop(n - 1, acc + 1)
```

のように調整する。

大事なのは、

```text
- top-level direct recursion ではなく local named recursion
- `MakeRecursiveClosure` を実際に踏む
- effect なしでも通る小さい例
```

にすることだねぇ。

---

# 6. block syntax の `undefined name 'n'` は別 issue

報告の `case ({ block }).once:` で `undefined name 'n'` になる件は、Phase F から切り離していい。

これは source / name resolution 側のバグっぽい。
今やっている CPS/native undet とは別 ticket にする。

メモとしては、

```text
TODO: block expression inside method receiver / case scrutinee loses local binding scope
```

くらいでよさそう。

---

# 7. 次に彼へ伝える指示

そのまま渡せる形にすると、これかなぁ。

```text
今の failing case は、std::undet.once 本体というより、
helper function work(): int の effectful body が Thunk のまま root へ漏れている問題です。

やること:
1. eval 側で root thunk を無条件 force しない。
2. lowering 側で return type / expected type が non-thunk の return site に ForceThunk を挿む。
3. まず入れる場所:
   - FunctionLowerer::lower_root / binding body return
   - root expression return
   - lower_lambda / lower_recursive_lambda body return
4. expected type が Thunk の場合は絶対に force しない。
5. Unknown / Fun / type var などは最初は force しない方が安全。
6. ForceThunk は non-thunk value では no-op のままにする。
7. work().once + guard の debug test を CPS eval → CPS repr eval → Cranelift の順に再実行する。

今は ListAppend/ListUncons や object/exe に進まない。
まず root thunk leak を解消する。
```

---

# 8. 次の成功条件

まずこれ。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_std_undet_once_skip_eval_layers -- --nocapture
```

期待:

```text
Layer 1 CPS eval: OK
Layer 2 CPS repr eval: OK
Layer 3 Cranelift: OK
```

次に、追加された3本の `std::undet.once` regression を unignore。

```text
- first rejected choice -> 2
- all rejected -> nil -> 0
- two nested choices -> VM compare
```

これが通ったら、`std::undet.once` は「たまたま最初の選択が通った」ではなく、**queue / resumption / reject path をちゃんと踏んだ** と言える。

---

# りなの判断

質問 1 への答えは明確で、**Phase F.5 step 5 は実装すべき**。
ただし evaluator で root thunk を force するのではなく、lowering の return site に入れる。

質問 2 は、切り分けテストは有用だけど、今は後回しでいい。
まず return-demand forcing を入れる。

質問 3 は、recursive closure regression は `with: our loop` 系で書くのがよさそう。
`sum_down` は今は monomorphizer / residual polymorphism に引っかかっていて、`MakeRecursiveClosure` regression としてはノイズが大きいねぇ。
