うん、これは **計画に少し変更あり** だよ〜。
ただし大きな方針は変えなくていい。むしろ、今回の debug で **次の一手がかなり正確に絞れた** ねぇ。

今やるべきことは、`ListAppend` / `ListUncons` や Cranelift helper に進む前に、まずこれ。

> **「thunk 型の引数を遅延する」は成功した。
> 次は「thunk が返ってきたとき、非-thunk が欲しい文脈では force する」を入れる。**

いまは `k true` の eager resume は直っている。
でもその結果、今度は root / call result に **thunk value が漏れている**。最新コミットにも、`root_0` が `Thunk(owner=root_0, entry=cont(1))` を返していて、期待される `Plain(opt::just(1))` になっていない、と書かれているねぇ。

---

# いまの状況の解釈

## 直ったもの

Phase F.1-F.4 で、`loop(k true, queue)` の `k true` は即時 `Resume` ではなく、`MakeThunk` に包まれるようになった。これは正しい。
`std::undet.once` の `loop x [] with: our loop(x, queue) = catch x: ...` では、`x` は `[_] _` なので、`k true` は次の `loop` の `catch x:` 内で force されるべきだからねぇ。`std::undet.once` の実装も、`branch(), k -> loop(k true, append queue [k])` という形でまさにそれを要求している。

## いま残っているもの

今はこうなっている。

```text
root_0:
    MakeThunk cont(1)
    Return Thunk(cont(1))
```

みたいな形で、**評価されるべき thunk が root の戻り値として漏れている**。

これは「第一級 thunk」としては一見よさそうに見えるけど、今回の root は `case (each [1,2,3]).once: ...` で最終的に `int` を返すはずなので、thunk のまま返るのはおかしい。

つまり今の bug は、

```text
thunk-typed argument を MakeThunk にするところは正しい
しかし non-thunk result が欲しい文脈で ForceThunk していない
```

だと思う。

---

# 計画変更の要点

## 変更前

前の計画では、

1. thunk-typed param を MakeThunk に包む
2. `ListAppend` / `ListUncons` を CPS value domain 対応にする
3. Cranelift helper を足す

という流れだった。

## 変更後

今は間にこれを挟む。

```text
1. thunk-typed param を MakeThunk に包む  ← 完了
2. non-thunk result demand で ForceThunk する  ← 次に最優先
3. ListAppend / ListUncons を CPS value domain 対応にする
4. Cranelift helper を足す
```

この **2** が今の blocker だねぇ。

---

# 絶対にやってはいけない修正

まず、彼にこれを強く伝えてほしい。

## 1. `eval_cps_module` が root thunk を勝手に force する修正は危険

たとえば、

```rust
fn eval_cps_module(...) {
    let value = eval_function(...)?;
    if value is Thunk { force it }
}
```

みたいに root で全部 force するのは、第一級 thunk の前提と相性が悪い。

将来、本当に thunk を値として返す root があるかもしれない。
だから「root だから全部 force」は避けたい。

## 2. `lower_expr_as_thunk_value` を戻してはいけない

`k true` を `MakeThunk` にしたこと自体は正しい。
ここを戻すと `MissingHandler in each__mono0` に逆戻りする。

## 3. `stop wrapping at root boundary` を雑にやらない

最新コミットのメッセージには「abort を wrap thunk の force に通すか、root boundary で wrap しないか」とあるけど、後者は危ない。

`each [1,2,3]` を `once` に渡すための thunk は必要。
root boundary で wrap を止めるなら、**それが本当に root 全体の余計な thunk なのか、once の引数 thunk なのか** を dump で確認してからにするべき。

---

# 次にやるべき実装

## Step 1: `cont(1)` の中身を分類する

まず debug dump で `root_0` が返している `Thunk(entry=cont(1))` の中身を確認する。

見るべき分類はこれ。

### Case A: `cont(1)` が `each [1,2,3]` だけを実行している

この場合、それは **once に渡すべき引数 thunk が root に漏れている**。
つまり、`once` の call / apply chain がどこかで完了していない。

この場合は、root で force しても正しくならない可能性が高い。
force したら handler なしで `each` が perform して、また `MissingHandler` になる。

### Case B: `cont(1)` が `once` / `loop` / `catch` 全体を実行している

この場合、それは **root 全体を包む thunk が force されていない**。
この場合は root result demand による `ForceThunk` が正しい。

### Case C: `cont(1)` が `once_mono1` の返り値 thunk

この場合、`once_mono1` の call result が force されていない。
`DirectCall` / `ApplyClosure` の **result normalization** が必要。

今の報告では Case C が一番ありそう。

---

# Step 2: result demand による `ForceThunk` を入れる

今回の新しい helper はこれ。

```rust
fn force_if_non_thunk_demand(
    &mut self,
    value: CpsValueId,
    expected_ty: &runtime::Type,
) -> CpsValueId {
    if is_thunk_type(expected_ty) {
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

`ForceThunk` は thunk なら force、plain / closure / resumption / list / tuple / variant なら no-op で返る設計にしておく。
すでに evaluator 側で no-op になっているならそのままでいい。

重要なのは、

```text
期待型が Thunk なら force しない
期待型が non-Thunk なら ForceThunk を挟む
```

というルール。

これなら第一級 thunk を壊しにくい。

---

# Step 3: `ApplyClosure` の result にも force を入れる

今は thunk-typed **argument** には対応した。
でも今回必要なのは **result** だねぇ。

`lower_apply` をこうする。

```rust
fn lower_apply(
    &mut self,
    expr: &runtime::Expr,
    callee: &runtime::Expr,
    arg: &runtime::Expr,
) -> CpsLowerResult<CpsValueId> {
    let param_ty = apply_param_type(callee);

    let closure = self.lower_expr(callee)?;
    let arg = self.lower_call_arg(arg, param_ty.as_ref())?;

    let dest = self.fresh_value();
    self.current.stmts.push(CpsStmt::ApplyClosure {
        dest,
        closure,
        arg,
    });

    Ok(self.force_if_non_thunk_demand(dest, &expr.ty))
}
```

ポイントは、`expr.ty` を見ること。
`callee.ty` ではなく、**apply expression 全体の型** だよ〜。

たとえば、

```yulang
loop(k true, queue)
```

の1段目 `loop(k true)` は関数を返すので force しても no-op のはず。
2段目 `loop(k true, queue)` は最終結果を返すので、もし thunk が返ってきているなら force される。

`ForceThunk` が non-thunk no-op なら、多少多めに挿んでも安全。
ただし expected type が `Thunk` のときは絶対に挿まない。

---

# Step 4: `DirectCall` の result も同じ helper に統一する

DirectCall にはすでに `direct_call_result_needs_force` があると思う。
でもこの機会に、ApplyClosure と同じ demand rule に寄せるといい。

```rust
let dest = self.fresh_value();
self.current.stmts.push(CpsStmt::DirectCall { dest, target, args });

let dest = self.force_if_non_thunk_demand(dest, &expr.ty);
return Ok(dest);
```

既存の `direct_call_result_needs_force(expr, info)` は残してもいいけど、今回の root thunk leak は **result context** の問題なので、`expr.ty` based の force を入れたほうが強い。

---

# Step 5: root / function return にも guard を入れる

最後の保険として、root や function body の `Return(value)` 前にも入れる。

ただし、ここも **return type が Thunk なら force しない**。

```rust
fn finish_function_return(
    &mut self,
    value: CpsValueId,
    ret_ty: &runtime::Type,
) {
    let value = self.force_if_non_thunk_demand(value, ret_ty);
    self.terminate(CpsTerminator::Return(value));
    self.finish_current();
}
```

使う場所:

```text
- lower_root
- lower_binding の body return
- lower_lambda / lower_recursive_lambda の body return
- finish_handled_value / finish_resumed_handled_value は慎重に
```

`finish_handled_value` に入れる場合は、handler value arm が thunk を返す設計を壊さないよう、expected type を持っている時だけにする。

最初は root / binding / apply / direct call に限定してよさそう。

---

# Step 6: Aborted propagation を確認する

`ForceThunk` した thunk の中で `sub::return` が起きると、`Aborted(value)` が返る。
最新の CPS evaluator は `Aborted` を `DirectCall`, `ApplyClosure`, `ForceThunk`, `Resume`, `ResumeWithHandler` で伝播するようになっている。

だから、`ForceThunk` result をこう扱うこと。

```rust
CpsStmt::ForceThunk { dest, thunk } => {
    let result = force(...)?;
    if matches!(result, CpsRuntimeValue::Aborted(_)) {
        return Ok(result);
    }
    write_value(&mut values, *dest, result);
}
```

これはもう入っている可能性が高い。
入っていなければ必須。

Cranelift 側も `return_if_abort_active` が入っているので、ForceThunk helper の直後にも abort check が必要。これは abort propagation commit の方向と一致している。

---

# Step 7: その後で `ListAppend` / `ListUncons`

`root thunk leak` が直ったら、たぶん次に `ListAppend` / `ListUncons` で詰まる。
最新の first-class container commit では `ListEmpty`, `ListSingleton`, `ListMerge` は CPS value list を直接作れるけど、`ListAppend` / `ListUncons` はまだ VM primitive fallback 側に残っているように見える。

`std::undet.once` は `std::list::append queue [k]` と `std::list::uncons queue` を使うので、ここは必ず必要。

ただし、今の root thunk leak より後でいい。

---

# 次セッションの作業順

彼にはこう伝えるのがよさそう。

```text
次は ListAppend/ListUncons ではなく、まず root/call result に漏れている Thunk を force する。

やること:

1. debug dump で root_0 が返している Thunk(entry=cont(1)) の cont(1) の中身を分類する。
   - each 引数 thunk が漏れているのか
   - once/loop 全体の wrapper thunk なのか
   - once_mono1 の call result thunk なのか

2. force_if_non_thunk_demand(value, expected_ty) を実装する。
   - expected_ty が Thunk ならそのまま
   - expected_ty が non-Thunk なら CpsStmt::ForceThunk を挿む
   - ForceThunk は non-thunk value では no-op

3. lower_apply の ApplyClosure result に対して、expr.ty を使って force_if_non_thunk_demand を呼ぶ。
   - ApplyClosure は argument thunkization だけでなく result normalization も必要

4. DirectCall result にも同じ処理を入れる。
   - 既存の direct_call_result_needs_force だけに頼らない
   - expr.ty が non-thunk なら ForceThunk を挟む

5. root / binding return にも、return type が non-thunk の場合だけ ForceThunk を挟む。

6. debugs_std_undet_once_scalar_unwrapped_eval_layers を再実行。
   - まず CPS eval で root が Plain(opt::just(1)) になることを確認
   - その後 CPS repr eval
   - Cranelift はその後

7. 次に ListAppend / ListUncons を CPS value domain に入れる。
```

---

# 彼に渡す短い指示文

このまま貼っていいよ〜。

```text
今の root_0 returns Thunk 問題は、thunk-typed argument の wrap 自体ではなく、call/root result の demand forcing が足りない問題として扱ってください。

やってはいけないこと:
- lower_expr_as_thunk_value を戻さない
- eval_cps_module が root thunk を無条件に force する修正をしない
- root boundary で wrap を雑に止めない
- ListAppend/ListUncons に進む前に root thunk leak を放置しない

実装:
1. force_if_non_thunk_demand(value, expected_ty) を作る。
   expected_ty が Thunk なら何もしない。
   expected_ty が non-Thunk なら ForceThunk を挿む。
   ForceThunk は non-thunk value では no-op。

2. lower_apply の ApplyClosure result に対して、apply expression 全体の expr.ty を使って force_if_non_thunk_demand を呼ぶ。

3. DirectCall result にも同じ処理を入れる。

4. root / binding return の直前にも、return type が non-thunk なら ForceThunk を入れる。

5. debug dump で root_0 の Return が Thunk ではなく、ForceThunk 後の value になっていることを確認する。

6. debugs_std_undet_once_scalar_unwrapped_eval_layers を CPS eval → CPS repr eval の順で通す。

その後に ListAppend / ListUncons の CPS value domain 対応へ進む。
```

---

# りなの判断

計画の大筋は変えなくていい。
でも **次の優先順位は変わった**。

今すぐやるのは queue でも Cranelift helper でもなく、

> **non-thunk が要求される文脈で、漏れた thunk result を ForceThunk する**

だねぇ。

`k true` を遅延する修正は正しい。
その遅延された thunk が、適切な場所で force されていないのが今の問題だと思うよ〜。
