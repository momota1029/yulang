うん、これは **計画に変更あり** だねぇ。
ただし「大きく方針転換」ではなく、**Phase F の優先順位と実装ポイントがかなり絞れた**、という感じ。

結論から言うと、今はもう `std::undet.once` の queue や first-class resumption そのものより前に、

> **thunk 型の引数を eager に評価してはいけない**

を直すのが最優先だよ〜。

最新コミットでは、CPS evaluator / CPS repr evaluator に `List` / `Tuple` / `Variant` が入り、container が `CpsRuntimeValue` / `CpsReprRuntimeValue` を直接持つようになっている。さらに `ListSingleton` が `Resumption` を保持でき、resumption stored in list の regression は通った、と整理されているねぇ。

なので、第一級化の入口はかなり良い。
今の `MissingHandler` は、第一級 container が足りないというより、**`loop(k true, queue)` の `k true` が、次の `catch x:` の handler scope に入る前に Resume されている** のが原因だと思う。

---

# 今の根本原因

ユーザーが貼ってくれた dump はかなり決定的だねぇ。

```text
cont(6) (branch arm body):
    UninstallHandler(1)
    Literal V12 = true
    Resume V13 (resumption: V11, arg: V12)   ← k true を即時評価
    ApplyClosure V14 (closure: V2 = loop, arg: V13)
    Primitive V15 = ListSingleton(V11)
    DirectCall V16 = list::append(V5, V15)
    ApplyClosure V17 (closure: V14, arg: V16)
```

本来はこうでないといけない。

```text
cont(6) (branch arm body):
    UninstallHandler(1)
    MakeThunk V13 (entry: thunk_for_k_true)
    ApplyClosure V14 (closure: V2 = loop, arg: V13)
    Primitive V15 = ListSingleton(V11)
    DirectCall V16 = list::append(V5, V15)
    ApplyClosure V17 (closure: V14, arg: V16)

thunk_for_k_true:
    Literal true
    Resume ... k true ...
```

なぜなら `loop` の第一引数 `x` は `[_] _`、つまり thunk / computation だから。
`std::undet.once` の実装も `loop x [] with: our loop(x, queue) = catch x: ...` という形で、`x` を `catch` の中で実行する設計になっている。

だから `loop(k true, queue)` の `k true` は、**その場で Resume してはいけない**。
次の `loop` の `catch x:` が handler を install したあとに force されるべき。

---

# 新しい Phase F 計画

## Phase F.0: 今の debug test は残す

まず `debugs_std_undet_once_cps_shape` は残す。
これはすごく良い pin になってる。

この test は、今後も以下を検査するべき。

```text
- loop(k true, ...) の k true が Resume stmt として即時評価されていない
- k true が MakeThunk entry に入っている
- ApplyClosure loop の第一引数が thunk value になっている
- loop body の catch x が InstallHandler のあとに ForceThunk している
```

この regression がないと、また eager resume が戻ってくる。

---

## Phase F.1: formal parameter type を call lowering に渡す

今の修正方針どおり、`FunctionInfo` に param types を持たせるのは正しい。
ただし、**DirectCall だけでは足りない**。dump では `loop` が `ApplyClosure` になっているからねぇ。

### 追加する構造

`cps_lower.rs` の `FunctionInfo` をこういう形にする。

```rust
#[derive(Debug, Clone)]
struct FunctionInfo {
    name: String,
    arity: usize,
    params: Vec<runtime::Type>,
    ret: runtime::Type,
}
```

既存の `ret` は残す。
`params` を追加する。

### param type の取り方

`binding_function_info` で、binding の callable spine から param 型を集める。

擬似コード:

```rust
fn binding_function_info(binding: &runtime::Binding) -> Option<(core_ir::Path, FunctionInfo)> {
    if let runtime::ExprKind::PrimitiveOp(op) = binding.body.kind {
        return Some((
            binding.name.clone(),
            FunctionInfo {
                name: path_name(&binding.name),
                arity: primitive_arity(op),
                params: primitive_param_types(op),
                ret: runtime::Type::unknown(),
            },
        ));
    }

    let (params, body) = collect_callable_params(&binding.body);
    if params.is_empty() {
        return None;
    }

    let param_types = collect_fun_param_types(&binding.body.ty, params.len());

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

`collect_fun_param_types` は、型の function spine を剥がす helper。

```rust
fn collect_fun_param_types(ty: &runtime::Type, arity: usize) -> Vec<runtime::Type> {
    let mut result = Vec::new();
    let mut current = ty;

    while result.len() < arity {
        match current {
            runtime::Type::Fun { param, ret, .. } => {
                result.push((**param).clone());
                current = ret;
            }
            // 型 variant 名は実装に合わせる
            runtime::Type::Thunk { .. } => {
                break;
            }
            _ => break,
        }
    }

    while result.len() < arity {
        result.push(runtime::Type::unknown());
    }

    result
}
```

型 variant 名は実際の `runtime::Type` に合わせて調整する。

---

## Phase F.2: DirectCall の引数 lowering を thunk-aware にする

DirectCall は比較的簡単。

今がこうなら、

```rust
let args = args
    .into_iter()
    .map(|arg| self.lower_expr(arg))
    .collect::<CpsLowerResult<Vec<_>>>()?;
```

こうする。

```rust
let lowered_args = args
    .into_iter()
    .enumerate()
    .map(|(index, arg)| {
        let param_ty = info.params.get(index);
        self.lower_call_arg(arg, param_ty)
    })
    .collect::<CpsLowerResult<Vec<_>>>()?;
```

helper:

```rust
fn lower_call_arg(
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

注意点は、`arg.ty` ではなく **callee の formal param type** を見ること。
`k true` 自体の結果型は `int` かもしれないけど、渡し先の `x` が `[_] int` だから thunk 化する必要がある。

---

## Phase F.3: ApplyClosure の引数 lowering も thunk-aware にする

ここが今回いちばん重要。

LLM は「ApplyClosure には callee FunctionInfo がない」と言っているけど、すぐに closure metadata を入れる前に、まず **callee expression の型** を使うのが良いと思う。

source/runtime IR の `Apply { callee, arg }` には、たぶん `callee.ty` がある。
その `callee.ty` が function type なら、そこから第一引数の型を取れる。

### `lower_apply` をこう変える

今がこういう形だとする。

```rust
fn lower_apply(
    &mut self,
    callee: &runtime::Expr,
    arg: &runtime::Expr,
) -> CpsLowerResult<CpsValueId> {
    let closure = self.lower_expr(callee)?;
    let arg = self.lower_expr(arg)?;
    let dest = self.fresh_value();

    self.current.stmts.push(CpsStmt::ApplyClosure {
        dest,
        closure,
        arg,
    });

    Ok(dest)
}
```

これをこうする。

```rust
fn lower_apply(
    &mut self,
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

    Ok(dest)
}
```

`apply_param_type`:

```rust
fn apply_param_type(callee: &runtime::Expr) -> Option<runtime::Type> {
    first_fun_param_type(&callee.ty)
}

fn first_fun_param_type(ty: &runtime::Type) -> Option<runtime::Type> {
    match ty {
        runtime::Type::Fun { param, .. } => Some((**param).clone()),

        // 必要なら Union/Intersection/Coerce/Unknown などを実装に合わせて見る
        _ => None,
    }
}
```

これで `loop(k true, queue)` の first apply は、

```text
callee = loop
callee.ty = [_] int -> list/res/...
param = [_] int
arg = k true
```

なので `lower_expr_as_thunk_value(k true)` が呼ばれる。

curried の二段目、

```text
ApplyClosure V17 (closure: V14, arg: V16)
```

では `callee.ty` が `queue_type -> result_type` のはずなので、`queue` は普通に評価される。

---

# ここで closure metadata は必要か？

短期的には **不要** だと思う。

ApplyClosure の lowering 時点では、source/runtime IR の callee expression に型が残っているはず。
それを使えばよい。

ただし、将来的に closure を list から取り出して apply するようなケースでは、

```yulang
case std::list::uncons fs:
    just (f, _) -> f arg
```

の `f` にも型が付いている必要がある。
型推論がそれを保持しているなら問題ない。保持していないなら、そのとき初めて closure metadata や typed container の話になる。

なので今回の計画としては、

```text
短期:
  ApplyClosure は callee.ty から param type を取る

中期:
  callee.ty が Unknown になる first-class closure use case が出たら、
  CpsClosure に param shape metadata を持たせるか、
  runtime IR lowering 前に type evidence を保存する
```

でよいと思うよ〜。

---

# Phase F.4: `lower_expr_as_thunk_value`

ここは慎重に書く必要がある。

目的は、**expr をその場で評価せず、thunk entry に移すこと**。

```rust
fn lower_expr_as_thunk_value(
    &mut self,
    expr: &runtime::Expr,
) -> CpsLowerResult<CpsValueId> {
    // すでに thunk value ならそのまま lower してよい
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

    // ここで expr を「いまの call site」で評価してはいけない。
    // 新しい thunk continuation の中で lower する。
    let value = self.lower_expr(expr)?;
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

ここで注意。
以前の helper に、

```rust
if active_handler is Some && collect_expr_performed_effects(expr) ...
    lower_handled_body(...)
```

みたいな処理があるなら、**thunk-typed call argument 用には使わない方が安全**。
`k true` は次の `loop` の `catch x:` で捕まるべきなので、作成時の handler context で静的に処理しない。

つまり helper を分けてもいい。

```rust
fn lower_expr_as_call_thunk_arg(...)
fn lower_expr_as_handler_body_thunk(...)
```

`loop(k true, queue)` 用は前者。
**force site の handler stack に任せる**。

---

# Phase F.5: dump の成功形

修正後の dump はこうなるべき。

```text
cont(6) (branch arm body):
    UninstallHandler(1)
    MakeThunk V13 (entry: cont_thunk_k_true)
    ApplyClosure V14 (closure: V2 = loop, arg: V13)
    Primitive V15 = ListSingleton(V11)
    DirectCall V16 = list::append(V5, V15)
    ApplyClosure V17 (closure: V14, arg: V16)

cont_thunk_k_true:
    Literal true
    Resume ... k true ...
    Return ...
```

この形になったら、`k true` が次の `loop` の `catch x:` handler scope で force される余地ができる。

---

# Phase F.6: `ListAppend` / `ListUncons` を CPS value 対応にする

今の最新コミットでは `ListEmpty` / `ListSingleton` / `ListMerge` は CPS-value list を直接構築している。
でも `std::undet.once` が使っているのは `append queue [k]` と `uncons queue`。

なので、ここも必須。

## `eval_cps_primitive`

```rust
match op {
    PrimitiveOp::ListAppend => {
        expect_arity(op, &args, 2)?;
        let mut iter = args.into_iter();
        let list = iter.next().unwrap();
        let value = iter.next().unwrap();
        append_or_extend_cps_list(op, list, value)
    }

    PrimitiveOp::ListUncons => {
        expect_arity(op, &args, 1)?;
        let list = args.into_iter().next().unwrap();
        uncons_cps_list_as_opt(op, list)
    }

    ...
}
```

## append

`std::list::append queue [k]` の第二引数は list なので、concat として扱える必要がある。

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
        other => {
            items.push(other);
        }
    }

    Ok(CpsRuntimeValue::List(Rc::new(items)))
}
```

## uncons

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

タグ名は VM の `std::list::uncons` が返す `std::opt::opt::nil` / `just` と一致させること。
ここは一度 VM primitive の結果を print/debug して確認したほうがいい。

同じ実装を `eval_cps_repr_primitive` にも入れる。

---

# Phase F.7: CPS eval / CPS repr eval の成功条件

この順で通す。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_std_undet_once_cps_shape -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_std_undet_once_scalar_unwrapped_eval_layers -- --nocapture
```

期待:

```text
CPS eval == VM
CPS repr eval == VM
```

まだ Cranelift は後でよい。

---

# Phase F.8: Cranelift 側の対応

CPS eval / repr eval が通ったら Cranelift。

`cps_runtime.rs` にはすでに `YulangCpsI64HeapValue::Tuple`, `Variant`, `List(Vec<i64>)` がある。これは first-class CPS container の方向として使える。

必要なのは `ListAppend` / `ListUncons` helper。

## `yulang_cps_list_append_i64`

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

## `yulang_cps_list_uncons_i64`

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

`tag_hash` が private なら内部 helper として使うか、既存 variant helper の形式に合わせる。

## Cranelift lowering

`PrimitiveOp::ListAppend` / `PrimitiveOp::ListUncons` を helper call に落とす。

```rust
PrimitiveOp::ListAppend => {
    let args = read_values(...)?;
    let callee = declare_helper("yulang_cps_list_append_i64", ...)?;
    let call = builder.ins().call(callee, &[args[0], args[1]]);
    let result = builder.inst_results(call)[0];
    builder.def_var(variable(dest), result);
}

PrimitiveOp::ListUncons => {
    let args = read_values(...)?;
    let callee = declare_helper("yulang_cps_list_uncons_i64", ...)?;
    let call = builder.ins().call(callee, &[args[0]]);
    let result = builder.inst_results(call)[0];
    builder.def_var(variable(dest), result);
}
```

---

# 計画変更のまとめ

## 変更なし

大枠はそのまま。

```text
1. std::undet.each + local once_dfs
2. first-class CPS value domain
3. std::undet.once scalar-unwrapped
4. non-scalar print / list / logic
```

## 変更あり

Phase F の中身が具体化した。

旧:

```text
std::undet.once の resumption queue を実装する
```

新:

```text
1. thunk-typed parameter への call argument を MakeThunk で包む
2. 特に ApplyClosure で callee.ty から formal param type を読む
3. ListAppend / ListUncons を CPS value domain 対応にする
4. その後に Cranelift helper を足す
```

つまり、今すぐ closure metadata まで行く必要はなさそう。
まずは **ApplyClosure の callee expression type から param type を取る** のが一番小さくて正しいと思うよ〜。

---

# 別LLへの更新指示

そのまま渡すならこれ。

```text
Phase F の根本原因は特定済み。

dump:
  branch arm body で loop(k true, append queue [k]) が lowering されると、
  k true が Resume stmt として即時評価されている。
  しかし loop の第一引数 x は Thunk type ([_] _)、loop body の catch x が
  handler を install してから force する設計なので、k true は MakeThunk に
  包まれて loop に渡される必要がある。

最優先作業:
1. FunctionInfo に params: Vec<runtime::Type> を追加。
2. DirectCall の引数 lowering で formal param type が Thunk なら lower_expr_as_thunk_value(arg) を使う。
3. ApplyClosure でも callee.ty から first function param type を取り、Thunk なら lower_expr_as_thunk_value(arg) を使う。
4. lower_expr_as_thunk_value は expr を即時評価せず、新しい continuation に expr body を入れて CpsStmt::MakeThunk を返す。
5. active_handler で lower_handled_body しない。force site の handler stack に任せる。
6. dump が Resume-before-ApplyClosure ではなく MakeThunk-before-ApplyClosure になったことを確認。
7. ListAppend / ListUncons を eval_cps_primitive / eval_cps_repr_primitive に追加。
8. CPS eval / CPS repr eval で std::undet.once scalar-unwrapped を通す。
9. その後 Cranelift の yulang_cps_list_append_i64 / yulang_cps_list_uncons_i64 を実装。

禁止:
- k true を call argument lowering で即時 Resume しない。
- ApplyClosure を無視して DirectCall だけ直さない。
- std::undet.once 専用 ContinuationArray を作らない。
- VmValue::List に Resumption を混ぜない。
```

---

# りなの見立て

かなり良い進み方だよ〜。
今の失敗は「わからない」ではなく、**`k true` が eager に resume されている** という具体的な lowering bug まで pin されている。

なので計画はこう。

```text
今すぐ:
  thunk-typed parameter に渡す式を MakeThunk 化する

次:
  ListAppend / ListUncons を CPS value domain に入れる

その次:
  Cranelift helper を合わせる

最後:
  std::undet.once scalar-unwrapped を unignore
```

これで `std::undet.once` はかなり近づくと思うねぇ。
