うん、ここまで来たなら、計画をもう一段切り直したほうがいいねぇ。
今の報告を見る限り、**第一級値ドメイン化そのものはかなり正しい方向に進んでいる**。ただ、`std::undet.once` の失敗は「resumption が list に入らない」だけではなく、**`once` の recursive handler loop の thunk 引数・handler scope・再帰呼び出しの組み合わせ**で、Milestone 6 の問題が別の形で再発しているように見えるよ〜。

最新の `native-undet-plan.md` では、Milestone 7 までは完了扱いで、次は CPS runtime value domain を広げて resumptions / closures / thunks が `List` / `Tuple` / `Variant` / function arguments を通れるようにする、と整理されている。
さらに最新コミットでは、`CpsRuntimeValue::List` / `Tuple` / `Variant` と `CpsReprRuntimeValue` 側の同等物が入り、`ListSingleton` が resumption を保持できるようになり、resumption-in-list regression は通った。ただし `std::undet.once` は `std::undet::undet::each__mono0` で `MissingHandler` になっている、と明記されている。

なので、次はこう進めるのがよさそう。

---

# 新しい進捗計画: `std::undet.once` を通すための Phase F 再設計

## 現在の完了地点

完了済みとして扱ってよいもの:

```text
✅ std::undet.each + local once_dfs
   - CPS eval OK
   - CPS repr eval OK
   - Cranelift OK

✅ first-class CPS value containers
   - CpsRuntimeValue::List / Tuple / Variant
   - CpsReprRuntimeValue::List / Tuple / Variant
   - ListSingleton can hold Resumption
   - resumption stored in list works

✅ Cranelift abort propagation
   - sub::return-style handler arm return is propagated
```

このあたりは GitHub 上の latest commit と plan の記述と一致している。

未完了:

```text
❌ std::undet.once scalar-unwrapped
   - CPS eval で MissingHandler
   - 場所: std::undet::undet::each__mono0
```

---

# 1. まず原因の仮説

`std::undet.once` は標準実装でこうなっているねぇ。

```yulang
pub once(x: [_] _) = loop x [] with:
    our loop(x: [_] _, queue) = catch x:
        branch(), k -> loop(k true, std::list::append queue [k])
        reject(), _ -> case std::list::uncons queue:
            std::opt::opt::nil -> std::opt::opt::nil
            std::opt::opt::just (k, queue) -> loop(k false, queue)
        v -> std::opt::opt::just v
```

つまり `branch` arm の中で `loop(k true, append queue [k])` している。`k` は queue に入る第一級 resumption で、あとで `k false` される。

今の `MissingHandler` は、おそらくこのどちらか。

## 仮説 A: `loop(k true, queue)` の `k true` が thunk 引数として遅延されず、呼び出し前に評価されている

`loop` の第一引数は `x: [_] _`、つまり thunk/computation。
本来は `k true` を **thunk として渡し**、次の `loop` の `catch x:` の中で force される必要がある。

でも lowering が direct call の引数を普通に `lower_expr(arg)` していると、

```text
loop(k true, queue)
```

の `k true` が caller 側で即時 resume される。
その resume の中で `each__mono0` が branch/reject を投げると、まだ次の `loop` の handler が install されていないので `MissingHandler` になる。

これが一番ありそう。

## 仮説 B: recursive `loop` の `catch x:` handler が install される前に thunk が force されている

似ているけど、こちらは `ForceThunk` の位置の問題。
`loop` に入った後でも、`InstallHandler` より前に `x` を force していると同じく handler が見えない。

## 仮説 C: `InstallHandler` / `UninstallHandler` が handler arm / recursive call の前後で早く pop されている

`once` は recursive local function + handler arm body + recursive call なので、handler stack の lifetime が短すぎると落ちる。

---

# 2. 最初に追加するデバッグテスト

今ある Phase F debug regression をさらに分割する。

```rust
#[test]
#[ignore = "Phase F debug: inspect std::undet.once lowering around loop(k true, queue)"]
fn debugs_std_undet_once_cps_shape() {
    let source = r#"
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#;

    run_with_large_stack(|| {
        let module = runtime_module_from_source_with_options(
            source,
            native_default_source_options(),
        ).expect("runtime module");

        let cps = crate::cps_lower::lower_cps_module(&module)
            .expect("CPS lowering");

        crate::cps_validate::validate_cps_module(&cps)
            .expect("CPS validation");

        let dump = format!("{cps:#?}");
        eprintln!("{dump}");

        // まず形だけ見る。必要なら名前は実際の dump に合わせる。
        assert!(
            dump.contains("std::undet::undet::once")
                || dump.contains("once"),
            "dump should contain once lowering"
        );
        assert!(
            dump.contains("InstallHandler"),
            "catch x should install a handler before forcing x"
        );
        assert!(
            dump.contains("MakeThunk"),
            "recursive loop(k true, queue) should pass k true as a thunk, not evaluate it eagerly"
        );
    });
}
```

この dump で確認するポイントは3つ。

```text
1. once loop function の catch x の直前に InstallHandler があるか
2. loop(k true, append queue [k]) の k true が MakeThunk になっているか
3. DirectCall loop の引数に Resume の結果が直接渡っていないか
```

ここで `k true` が `Resume` として direct call 前に出ていたら、修正箇所はほぼ確定だよ〜。

---

# 3. 最優先修正: thunk-typed function parameter の引数 lowering

## 目的

関数が thunk parameter を要求している場合、direct call の引数を即時評価しない。

例:

```yulang
loop(k true, queue)
```

ここで `loop` の第一引数 `x` は `[_] _`。
だから `k true` は即時 resume ではなく、thunk として渡すべき。

---

## 3.1 `FunctionInfo` に parameter types を持たせる

今 `FunctionInfo` には少なくとも `arity` と `ret` があるはず。
ここに `params` を足す。

```rust
#[derive(Debug, Clone)]
struct FunctionInfo {
    name: String,
    arity: usize,
    params: Vec<runtime::Type>,
    ret: runtime::Type,
}
```

`binding_function_info` で、binding の function type から param types を取る。

擬似コード:

```rust
fn binding_function_info(binding: &runtime::Binding) -> Option<(core_ir::Path, FunctionInfo)> {
    let (params, body) = collect_callable_params(&binding.body);
    if params.is_empty() {
        return None;
    }

    let param_types = collect_function_param_types(&binding.body.ty, params.len());

    Some((
        binding.name.clone(),
        FunctionInfo {
            name: path_name(&binding.name),
            arity: params.len(),
            params: param_types,
            ret: body.ty.clone(),
        },
    ))
}
```

`collect_function_param_types` はこんな形。

```rust
fn collect_function_param_types(ty: &runtime::Type, arity: usize) -> Vec<runtime::Type> {
    let mut result = Vec::new();
    let mut current = ty;

    while result.len() < arity {
        match current {
            runtime::Type::Fun { param, ret, .. } => {
                result.push((**param).clone());
                current = ret;
            }
            _ => {
                result.push(runtime::Type::unknown());
                break;
            }
        }
    }

    while result.len() < arity {
        result.push(runtime::Type::unknown());
    }

    result
}
```

型 variant 名は実際の `runtime::Type` に合わせて調整してねぇ。

---

## 3.2 direct call 引数 lowering を param type aware にする

今はたぶんこう。

```rust
let args = args
    .into_iter()
    .map(|arg| self.lower_expr(arg))
    .collect::<CpsLowerResult<Vec<_>>>()?;
```

これをこうする。

```rust
let lowered_args = args
    .into_iter()
    .enumerate()
    .map(|(index, arg)| {
        let param_ty = info.params.get(index);
        self.lower_direct_call_arg(arg, param_ty)
    })
    .collect::<CpsLowerResult<Vec<_>>>()?;
```

新規 helper:

```rust
fn lower_direct_call_arg(
    &mut self,
    arg: &runtime::Expr,
    param_ty: Option<&runtime::Type>,
) -> CpsLowerResult<CpsValueId> {
    if param_ty.is_some_and(is_thunk_type) {
        return self.lower_expr_as_thunk_value(arg);
    }

    self.lower_expr(arg)
}

fn is_thunk_type(ty: &runtime::Type) -> bool {
    matches!(ty, runtime::Type::Thunk { .. })
}
```

---

## 3.3 `lower_expr_as_thunk_value`

これは重要。

```rust
fn lower_expr_as_thunk_value(
    &mut self,
    expr: &runtime::Expr,
) -> CpsLowerResult<CpsValueId> {
    // すでに thunk expression なら普通に lower してよい
    if matches!(expr.ty, runtime::Type::Thunk { .. }) {
        return self.lower_expr(expr);
    }

    let entry = self.fresh_continuation();
    let dest = self.fresh_value();

    let saved_current = std::mem::replace(
        &mut self.current,
        ContinuationBuilder::new(entry, Vec::new()),
    );
    let saved_locals = self.locals.clone();
    let saved_local_exprs = self.local_exprs.clone();
    let saved_resumptions = self.resumptions.clone();

    // expr が effectful なら、現在の active_handler context を使って
    // thunk body として lowering する。
    let value = if let Some(context) = self.active_handler.clone()
        && !collect_expr_performed_effects(expr).is_empty()
    {
        let value_cont = self.fresh_continuation();
        let value = self.fresh_value();

        self.lower_handled_body(
            expr,
            &context.expected_effects,
            context.handler,
            Some(value_cont),
        )?;

        self.current = ContinuationBuilder::new(value_cont, vec![value]);
        value
    } else {
        self.lower_expr(expr)?
    };

    self.terminate(CpsTerminator::Return(value));
    self.finish_current();

    self.locals = saved_locals;
    self.local_exprs = saved_local_exprs;
    self.resumptions = saved_resumptions;
    self.current = saved_current;

    self.current.stmts.push(CpsStmt::MakeThunk {
        dest,
        entry,
    });

    Ok(dest)
}
```

ここは既存の `lower_lambda` / `lower_thunk` helper があるなら、それを再利用する。
大事なのは、**`k true` をここで評価しない** こと。

---

## 3.4 この修正後に確認する dump

`loop(k true, append queue [k])` 周辺で、

```text
MakeThunk { entry: ... }  // k true の thunk
DirectCall loop [thunk, queue]
```

になっていること。

逆にこうならダメ。

```text
Resume { resumption: k, arg: true }
DirectCall loop [resume_result, queue]
```

---

# 4. 次の修正: `ListAppend` / `ListUncons` を CPS value domain に入れる

今の報告では、CPS primitive は `ListEmpty` / `ListSingleton` / `ListMerge` が CPS list を直接構築できる。
でも `std::undet.once` が使うのはこれ。

```yulang
std::list::append queue [k]
std::list::uncons queue
```

標準実装でも `append queue [k]` と `uncons queue` が使われている。

なので `ListAppend` と `ListUncons` を **必ず CPS value 対応**にする。

## 4.1 `eval_cps_primitive` に追加

```rust
match op {
    PrimitiveOp::ListAppend => {
        expect_arity(op, &args, 2)?;
        let mut iter = args.into_iter();
        let list = iter.next().unwrap();
        let value = iter.next().unwrap();
        append_cps_list(op, list, value)
    }

    PrimitiveOp::ListUncons => {
        expect_arity(op, &args, 1)?;
        let list = args.into_iter().next().unwrap();
        uncons_cps_list_as_opt(op, list)
    }

    ...
}
```

## 4.2 append

```rust
fn append_cps_list(
    op: core_ir::PrimitiveOp,
    list: CpsRuntimeValue,
    value: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let mut items = control_list_items(op, list)?;
    items.push(value);
    Ok(CpsRuntimeValue::List(Rc::new(items)))
}
```

注意: `std::list::append queue [k]` の第二引数が list の場合、Yulang の `append` が「item 追加」なのか「list append」なのか確認する。
もし `append queue [k]` が list concat なら、`ListAppend` ではなく `ListMerge` / `ListConcat` に落ちている可能性がある。dump で primitive op を必ず確認する。

必要なら両方対応:

```rust
fn append_or_extend_cps_list(
    op: core_ir::PrimitiveOp,
    list: CpsRuntimeValue,
    value: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let mut items = control_list_items(op, list)?;

    match value {
        CpsRuntimeValue::List(values) => {
            items.extend(values.iter().cloned());
        }
        other => items.push(other),
    }

    Ok(CpsRuntimeValue::List(Rc::new(items)))
}
```

## 4.3 uncons

```rust
fn uncons_cps_list_as_opt(
    op: core_ir::PrimitiveOp,
    list: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let items = control_list_items(op, list)?;

    if items.is_empty() {
        return Ok(CpsRuntimeValue::Variant {
            tag: core_ir::Name("nil".to_string()),
            value: None,
        });
    }

    let head = items[0].clone();
    let tail = CpsRuntimeValue::List(Rc::new(items[1..].to_vec()));

    Ok(CpsRuntimeValue::Variant {
        tag: core_ir::Name("just".to_string()),
        value: Some(Box::new(CpsRuntimeValue::Tuple(vec![
            head,
            tail,
        ]))),
    })
}
```

タグは要確認。
VM の `ListUncons` が返す `std::opt::opt::nil` / `just` の tag と完全に合わせる。名前だけで合うなら `nil` / `just` でいいけど、path が必要なら VM primitive から tag を確認する。

同じ修正を `eval_cps_repr_primitive` にも入れる。

---

# 5. `MissingHandler` がまだ出る場合の追加修正

`lower_expr_as_thunk_value` と `ListAppend` / `ListUncons` を入れても `MissingHandler` が出る場合、次は handler stack lifetime の問題。

## 5.1 `InstallHandler` が recursive `loop` の function body にあるか確認

CPS dump で `loop` function を見る。

期待:

```text
loop entry:
  InstallHandler(handler)
  ForceThunk(x)
  ...
```

NG:

```text
ForceThunk(x)
InstallHandler(handler)
...
```

または handler arm に入る前に:

```text
UninstallHandler(handler)
DirectCall loop(...)
```

になっている。

## 5.2 handler arm body で selected handler を外すのは正しいが、新しい loop は handler を install する必要がある

`branch(), k -> loop(k true, queue2)` の handler arm body は、選択された handler の外側で実行される。これはたぶん正しい。
ただし recursive `loop` call の内部で `catch x:` が新しい handler を install するので、`k true` はそこまで遅延されないといけない。

つまり、本丸はやはり **thunk param argument lowering**。

---

# 6. Cranelift へ進む前の成功条件

まず CPS eval / CPS repr eval で `std::undet.once scalar-unwrapped` を通す。

```rust
#[test]
#[ignore = "Phase F: std::undet.once scalar-unwrapped through CPS eval/repr eval"]
fn debugs_std_undet_once_scalar_unwrapped_eval_layers() {
    let source = r#"
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#;

    run_with_large_stack(|| {
        let module = runtime_module_from_source_with_options(
            source,
            native_default_source_options(),
        ).expect("runtime module");

        let cps = crate::cps_lower::lower_cps_module(&module)
            .expect("CPS lowering");
        crate::cps_validate::validate_cps_module(&cps)
            .expect("CPS validation");

        crate::cps_compare::compare_cps_module(&module)
            .expect("CPS eval == VM");

        let repr = crate::cps_repr::lower_cps_repr_module(&cps);
        let repr_values = crate::cps_repr::eval_cps_repr_module(&repr)
            .expect("CPS repr eval");

        let vm_results = runtime::compile_vm_module(module.clone())
            .expect("VM compile")
            .eval_roots()
            .expect("VM eval");

        let vm_value = match &vm_results[0] {
            runtime::VmResult::Value(v) => v.clone(),
            runtime::VmResult::Request(_) => panic!("VM gave request"),
        };

        assert_eq!(repr_values[0], vm_value);
    });
}
```

ここが通るまで Cranelift は触らない。

---

# 7. Cranelift 側: heap list の `append` / `uncons`

CPS eval / repr eval が通ったら、Cranelift。

`cps_runtime.rs` にはすでに `YulangCpsI64HeapValue::Tuple`, `Variant`, `List(Vec<i64>)` がある。これは CPS value container として良い方向。

必要な helper を追加・確認する。

## 7.1 append / concat helper

```rust
#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_append_i64(list: i64, value: i64) -> i64 {
    let list_value = unsafe { &*(list as *const YulangCpsI64HeapValue) };

    let YulangCpsI64HeapValue::List(items) = list_value else {
        return yulang_cps_list_empty_i64();
    };

    let mut new_items = items.clone();

    if is_heap_value(value) {
        let maybe_list = unsafe { &*(value as *const YulangCpsI64HeapValue) };
        if let YulangCpsI64HeapValue::List(values) = maybe_list {
            new_items.extend(values.iter().copied());
            return heap_value(YulangCpsI64HeapValue::List(new_items));
        }
    }

    new_items.push(value);
    heap_value(YulangCpsI64HeapValue::List(new_items))
}
```

`append queue [k]` が list concat なら上の挙動が必要。
単一 append なら push だけでよい。

## 7.2 uncons helper

```rust
#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_uncons_i64(list: i64) -> i64 {
    let value = unsafe { &*(list as *const YulangCpsI64HeapValue) };

    let YulangCpsI64HeapValue::List(items) = value else {
        return yulang_cps_variant_i64_0(tag_hash("nil"));
    };

    if items.is_empty() {
        return yulang_cps_variant_i64_0(tag_hash("nil"));
    }

    let head = items[0];
    let tail = heap_value(YulangCpsI64HeapValue::List(items[1..].to_vec()));
    let pair = yulang_cps_tuple_i64_2(head, tail);

    yulang_cps_variant_i64_1(tag_hash("just"), pair)
}
```

タグ hash は既存 `variant` helper と同じものを使う。
`register_tag_name` も必要なら `nil` / `just` を登録する。

---

## 7.3 Cranelift primitive lowering に追加

`cps_repr_cranelift.rs` で `PrimitiveOp::ListAppend` / `ListUncons` を lowering する。

擬似コード:

```rust
PrimitiveOp::ListAppend => {
    let helper = declare_import(
        jit,
        builder,
        "yulang_cps_list_append_i64",
        &[types::I64, types::I64],
        types::I64,
    )?;
    let args = read_values(builder, function, args)?;
    let call = builder.ins().call(helper, &[args[0], args[1]]);
    let result = builder.inst_results(call)[0];
    builder.def_var(variable(dest), result);
}

PrimitiveOp::ListUncons => {
    let helper = declare_import(
        jit,
        builder,
        "yulang_cps_list_uncons_i64",
        &[types::I64],
        types::I64,
    )?;
    let args = read_values(builder, function, args)?;
    let call = builder.ins().call(helper, &[args[0]]);
    let result = builder.inst_results(call)[0];
    builder.def_var(variable(dest), result);
}
```

`VariantTagEq` / `VariantPayload` / `TupleGet` はすでに heap variant / tuple helper を使えるはず。
ただし `VariantTagEq` の tag hash が VM/CPS eval と一致しているか確認する。

---

# 8. Phase F 完了条件

以下を unignore して通す。

```rust
compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift
```

コマンド:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native std_undet_once -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native once_scalar -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_repr -- --nocapture
```

期待:

```text
case (each [1,2,3]).once:
  nil -> 0
  just x -> x

=> 1
```

---

# 9. その後の Phase G: non-scalar print

Phase F では root を int に潰す。

```yulang
case (each [1,2,3]).once:
    nil -> 0
    just x -> x
```

その後に、

```yulang
(each [1,2,3]).once
```

をそのまま native executable で print する。

これは `opt int` の print が必要。
`YulangCpsI64HeapValue::Variant` / `Tuple` / `List` は print できるので、今の方向ならかなり近い。`cps_runtime.rs` には heap tuple / variant / list の print がすでにある。

ただし tag 表示や `std::opt::opt::just` の pretty print はあとでよい。

---

# 10. 別LLに渡す指示

そのまま渡せる形でまとめるねぇ。

```text
現在の状況:
- std::undet.each + local once_dfs は VM/CPS eval/CPS repr eval/Cranelift で通った。
- CpsRuntimeValue / CpsReprRuntimeValue に List/Tuple/Variant が入り、ListSingleton can hold Resumption。
- resumption stored in list regression は通った。
- std::undet.once scalar-unwrapped は MissingHandler in std::undet::undet::each__mono0 で失敗。

最重要仮説:
- std::undet.once の recursive loop で `loop(k true, queue)` の `k true` が thunk parameter として遅延されず、direct call 引数 lowering で即時 resume されている。
- `loop` の第一引数は `[_] _` なので、`k true` は MakeThunk として渡し、次の loop の `catch x:` の中で force されなければならない。

作業順:
1. CPS dump を見て `loop(k true, ...)` が Resume before DirectCall になっていないか確認。
2. FunctionInfo に params: Vec<runtime::Type> を追加する。
3. direct call lowering で callee param が Thunk 型なら、arg を lower_expr せず lower_expr_as_thunk_value で MakeThunk にする。
4. lower_expr_as_thunk_value は expr を評価せず、新しい continuation entry に expr body を入れて CpsStmt::MakeThunk を返す。
5. CPS eval / CPS repr eval で std::undet.once scalar-unwrapped を通す。
6. eval_cps_primitive / eval_cps_repr_primitive に ListAppend / ListUncons を CPS value domain で実装する。
   - ListAppend は list<resumption> を保持できること。
   - ListUncons は CpsRuntimeValue::Variant just(tuple(head, tail)) / nil を返すこと。
7. Cranelift cps_runtime.rs に yulang_cps_list_append_i64 / yulang_cps_list_uncons_i64 を追加。
8. cps_repr_cranelift.rs の primitive lowering に ListAppend / ListUncons を追加。
9. std::undet.once scalar-unwrapped regression を unignore する。

禁止:
- std::undet.once 専用 ContinuationArray を作らない。
- VmValue::List に Resumption を混ぜない。
- k true を direct call argument lowering で即時 Resume しない。
- Cranelift だけ先に直さない。
```

---

# りなの見立て

今の blocker は、第一級値ドメインの不足というより、**`once` の recursive loop が thunk-typed parameter を持つのに、direct call argument lowering が eager になっている疑い** が強い。

もちろん `std::undet.once` には `list<resumption>` が必要なので、`ListAppend` / `ListUncons` の CPS value 対応も必須。
でも `MissingHandler in each__mono0` という症状から見ると、まずは **`k true` が次の handler scope まで遅延されているか** を確認するのが一番大事だと思うよ〜。
