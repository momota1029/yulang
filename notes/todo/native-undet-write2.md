うん、今の状況だと **Milestone 6 以降で失敗している理由はかなりはっきりしてきている** よ〜。
そして、次に書くべきコードもだいぶ絞れる。

まず現状整理から言うねぇ。

## 現在地

`each_head` はもう通っている。最新コミットで、non-recursive helper である `each_head(xs): [choice] int` は inline され、返ってきた thunk が caller の handler scope 内で force されるようになっている。CPS eval / CPS repr eval / Cranelift JIT が VM と一致する、という状態に進んでいるねぇ。

一方で、`each_list` はまだ ignored regression として残っている。`native-undet-plan.md` でも、recursive helper like `each_list(xs): [choice] int` は inline されず、callee 側で `Perform` が known handler entry なしで出るため、caller の active handler frame を function boundary 越しに渡す必要がある、と整理されている。

つまり、今の失敗はこう。

```text
each_head:
  caller handler scope で inline
  -> thunk を caller handler scope で ForceThunk
  -> branch/reject が caller handler に届く
  -> OK

each_list:
  recursive なので inline できない
  -> callee function 内で thunk / Perform が作られる
  -> caller handler frame が callee に伝わらない
  -> Perform が handler entry を見つけられない
  -> NG
```

なので、次にやるべきことは **「recursive helper を inline しようとする」ではなく、「dynamic handler context を function call 境界で渡す」** だよ〜。

---

# 次の最重要方針

## Milestone 6 の本質

Milestone 6 は「recursive `each_list` を通す」ではなく、もっと正確にはこれ。

> **effectful thunk を返す non-inlined function call に、caller の active handler context を渡す。**

この文を設計の中心に置くといいよ〜。

`each_list` は recursive だから inline できない。
だから `each_head` と同じ方法、つまり caller 側で展開して ForceThunk するだけでは足りない。

必要なのは、callee の中で `choice::branch` / `choice::reject` が発生したときに、caller の `once_dfs_int` handler stack を参照できること。

---

# 実装案の全体像

やり方は大きく2つある。

## 案A: hidden dynamic context を function call に通す

これが本命。
CPS evaluator / CPS repr evaluator / Cranelift の function call に、`active_handlers` と `guard_stack` を渡す。

```text
DirectCall target(args)
```

を概念的にこうする。

```text
DirectCall target(dynamic_handler_stack, guard_stack, args)
```

ただし source-level の関数引数には見せない。native CPS runtime の hidden context として渡す。

## 案B: ForceThunk に caller handler frame を明示的に渡す

これは応急処置として使える。

```rust
CpsStmt::ForceThunk {
    dest,
    thunk,
}
```

をこう拡張する。

```rust
CpsStmt::ForceThunk {
    dest,
    thunk,
    handlers: Vec<CpsForceHandler>,
}
```

caller handler scope 内で force する場合に、現在の handler frame を `handlers` に入れる。
ただし、これは `ForceThunk` する call site がある場合には効くけど、callee 内で Perform が先に出る構造には弱い。`each_list` の recursive false branch が `each_list rest` を返すだけでなく、その中の thunk をまた force するなら一部効く。でも長期的には hidden context のほうが正しいと思う。

りなのおすすめはこう。

> **短期: ForceThunk に explicit handler context を持たせる。
> 中期: DirectCall / ApplyClosure に dynamic context を通す。
> Milestone 6 は中期の入口として扱う。**

---

# まずやるべき具体作業

## Step 1: 失敗を分解するテストを追加

今ある ignored test は Cranelift compare だけになっている可能性が高い。
まず、`each_list` を3段階に分けて失敗させるテストを足す。

```rust
#[test]
#[ignore = "Milestone 6 debug: each_list through CPS eval / repr eval / Cranelift"]
fn debugs_each_list_recursive_through_cps_stages() {
    let source = r#"
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my each_list(xs: std::list::list int): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, rest) -> case choice::branch ():
        true -> x
        false -> each_list rest

once_dfs_int { each_list [1, 2, 3] }
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

        eprintln!("{cps:#?}");

        let cps_values = crate::cps_eval::eval_cps_module(&cps)
            .expect("CPS eval");

        let repr = crate::cps_repr::lower_cps_repr_module(&cps);
        let repr_values = crate::cps_repr::eval_cps_repr_module(&repr)
            .expect("CPS repr eval");

        assert_eq!(cps_values, repr_values);

        compare_source_cps_repr_i64(source)
            .expect("CPS repr Cranelift compare");
    });
}
```

このテストで見ることは3つ。

```text
1. CPS eval で失敗するか
2. CPS repr eval で失敗するか
3. Cranelift だけで失敗するか
```

もし CPS eval で失敗するなら、まず `cps_eval.rs` の dynamic context propagation が足りない。
CPS repr eval でだけ失敗するなら、`cps_repr.rs` の lowering/evaluator が足りない。
Cranelift だけで失敗するなら、`cps_repr_cranelift.rs` / `cps_runtime.rs` の hidden context が足りない。

---

# Step 2: CPS evaluator の DirectCall に active context を渡す

まず interpreter で意味を合わせる。

今の `cps_eval.rs` の direct call は、おそらくこんな形に近い。

```rust
CpsStmt::DirectCall { dest, target, args } => {
    let args = args
        .iter()
        .map(|id| read_plain_value(function, &values, *id))
        .collect::<CpsEvalResult<Vec<_>>>()?;

    write_value(
        &mut values,
        *dest,
        CpsRuntimeValue::Plain(eval_function(module, target_function, args)?),
    );
}
```

これだと `eval_function` が空の handler stack / guard stack で callee を実行する。
だから recursive helper の callee が caller handler を見失う。

## 書くべきコード

`eval_function` を薄い wrapper にして、context 付き関数を作る。

```rust
fn eval_function(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<runtime::VmValue>,
) -> CpsEvalResult<runtime::VmValue> {
    let value = eval_function_with_context(
        module,
        function,
        args,
        Vec::new(),
        Vec::new(),
    )?;
    into_plain_value(function, CpsValueId(usize::MAX), value)
}

fn eval_function_with_context(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<runtime::VmValue>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
) -> CpsEvalResult<CpsRuntimeValue> {
    eval_continuations(
        module,
        function,
        function.entry,
        args.into_iter().map(CpsRuntimeValue::Plain).collect(),
        Vec::new(),
        active_handlers,
        guard_stack,
    )
}
```

そして `DirectCall` をこうする。

```rust
CpsStmt::DirectCall { dest, target, args } => {
    let target_function = function_by_name(module, target)?;
    let args = args
        .iter()
        .map(|id| read_plain_value(function, &values, *id))
        .collect::<CpsEvalResult<Vec<_>>>()?;

    let result = eval_function_with_context(
        module,
        target_function,
        args,
        active_handlers.clone(),
        guard_stack.clone(),
    )?;

    write_value(&mut values, *dest, result);
}
```

ここで重要なのは、**DirectCall は caller の dynamic context を callee に渡す** ということ。

これにより、`each_list` の callee 側で作られる thunk / Perform が caller の handler stack を見られるようになる。

---

# Step 3: ForceThunk の semantics を見直す

今の `ForceThunk` は、thunk に保存された handler stack だけで実行している可能性が高い。
でも `each_list` では、caller handler の中で force したい。

## ルール

`ForceThunk` はこう扱う。

```text
force-site active handler stack が空でなければ、それを優先する。
ただし thunk が明示的に captured handler frames を持っている場合は、
force-site stack の内側または外側に合成する。
```

最初の実装は単純でよい。

```rust
fn handler_stack_for_force(
    force_site: &[CpsHandlerFrame],
    thunk_handlers: &[CpsHandlerFrame],
) -> Vec<CpsHandlerFrame> {
    if !force_site.is_empty() {
        force_site.to_vec()
    } else {
        thunk_handlers.to_vec()
    }
}
```

そして `ForceThunk` をこうする。

```rust
CpsStmt::ForceThunk { dest, thunk } => {
    let value = read_value(function, &values, *thunk)?;
    let result = match value {
        CpsRuntimeValue::Thunk(thunk) => {
            let handlers = handler_stack_for_force(
                &active_handlers,
                thunk.handlers.as_ref(),
            );

            let guards = if !guard_stack.is_empty() {
                guard_stack.clone()
            } else {
                thunk.guard_stack.as_ref().clone()
            };

            eval_continuations(
                module,
                function,
                thunk.entry,
                Vec::new(),
                thunk.values.as_ref().clone(),
                handlers,
                guards,
            )?
        }
        value => value,
    };

    write_value(&mut values, *dest, result);
}
```

これは少し荒いけど、Milestone 6 には効く可能性が高い。

後で refined version にするなら、`CpsStmt::ForceThunk` に explicit handler frames を持たせる。

---

# Step 4: CPS repr evaluator も同じ修正をする

CPS eval だけ通しても意味がない。
`crates/yulang-native/src/cps_repr.rs` にも同じ DirectCall / ForceThunk semantics を入れる。

## 書くべき考え方

CPS repr eval でも、

```rust
DirectCall {
    target,
    args,
}
```

を処理するとき、callee を空 context で呼ばない。

```rust
let result = eval_repr_function_with_context(
    module,
    target_function,
    args,
    active_handlers.clone(),
    guard_stack.clone(),
)?;
```

また、`ForceThunk` も force-site context を使う。

```rust
let handlers = if !active_handlers.is_empty() {
    active_handlers.clone()
} else {
    thunk.handlers.clone()
};
```

この2つを CPS eval と CPS repr eval で揃える。

---

# Step 5: ここまでで Milestone 6 を Cranelift なしで通す

ここでまず、Cranelift なしのテストを通す。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_each_list_recursive_through_cps_stages -- --nocapture
```

期待としては、

```text
CPS eval OK
CPS repr eval OK
Cranelift NG
```

まで行けば大成功。

Cranelift NG のままでも、semantic model は固まっている。

---

# Step 6: Cranelift 側に hidden dynamic context を通す

ここが本番。

`each_list` が Cranelift で失敗する理由は、direct call 先の function が caller の handler stack / guard stack を知らないから。

## 実装方針

CPS repr Cranelift では、effectful function / thunk-returning function に hidden args を足す。

概念的にはこう。

```text
fn each_list(hidden_handler_stack, hidden_guard_stack, xs) -> thunk_or_value
```

root から呼ぶときは空 stack を渡す。

```text
each_list(empty_handler_stack(), empty_guard_stack(), xs)
```

handler scope 内から呼ぶときは current stack を渡す。

```text
each_list(current_handler_stack, current_guard_stack, xs)
```

---

## 6.1 ABI に dynamic context flag を足す

`CpsReprAbiFunction` かそれに相当する struct に、以下を足す。

```rust
pub struct CpsReprAbiFunction {
    pub name: String,
    ...
    pub needs_dynamic_context: bool,
}
```

判定関数を作る。

```rust
fn function_needs_dynamic_context(function: &CpsReprAbiFunction) -> bool {
    function_has_effect_flow(function)
        || function_returns_thunk(function)
        || function_has_force_thunk(function)
        || function_has_make_thunk(function)
}
```

具体的にはまず雑でよい。

```rust
fn function_needs_dynamic_context(function: &CpsReprAbiFunction) -> bool {
    !function.handlers.is_empty()
        || function.continuations.iter().any(|cont| {
            matches!(cont.terminator, CpsTerminator::Perform { .. })
                || cont.stmts.iter().any(|stmt| matches!(
                    stmt,
                    CpsStmt::MakeThunk { .. }
                        | CpsStmt::ForceThunk { .. }
                        | CpsStmt::Resume { .. }
                        | CpsStmt::ResumeWithHandler { .. }
                ))
        })
}
```

---

## 6.2 function signature に hidden args を足す

現在の scalar CPS repr function signature がこうなら、

```rust
fn function_signature(jit: &JITModule, function: &CpsReprAbiFunction) -> ir::Signature {
    let mut sig = jit.make_signature();
    sig.params.extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}
```

こうする。

```rust
fn function_signature(jit: &JITModule, function: &CpsReprAbiFunction) -> ir::Signature {
    let mut sig = jit.make_signature();

    if function.needs_dynamic_context {
        sig.params.push(AbiParam::new(types::I64)); // handler_stack
        sig.params.push(AbiParam::new(types::I64)); // guard_stack
    }

    sig.params.extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}
```

ただし root exported function は外部から呼ぶので、hidden args を要求しないほうがよい。
そのためには **internal function** と **root wrapper** を分けるのが安全。

簡単な暫定なら、root function wrapper で空 stack を作って internal entry continuation を呼ぶ。

---

## 6.3 Cranelift lowering context に current stack values を持たせる

lowering 中に current handler/guard stack の `ir::Value` を持つ。

```rust
struct LowerContext {
    handler_stack: Option<ir::Value>,
    guard_stack: Option<ir::Value>,
}
```

function entry で hidden args を読む。

```rust
let params = builder.block_params(entry_block).to_vec();

let (handler_stack, guard_stack, user_params_start) = if function.needs_dynamic_context {
    (Some(params[0]), Some(params[1]), 2)
} else {
    (None, None, 0)
};
```

ない場合は empty stack helper で作る。

```rust
let handler_stack = handler_stack.unwrap_or_else(|| {
    call_empty_handler_stack(jit, builder)
});

let guard_stack = guard_stack.unwrap_or_else(|| {
    call_empty_guard_stack(jit, builder)
});
```

---

## 6.4 DirectCall lowering で hidden args を渡す

現在の DirectCall lowering がこうなら、

```rust
let call = builder.ins().call(callee, &args);
```

こうする。

```rust
let mut call_args = Vec::new();

if callee.needs_dynamic_context {
    call_args.push(ctx.handler_stack);
    call_args.push(ctx.guard_stack);
}

call_args.extend(args);

let call = builder.ins().call(callee, &call_args);
```

ここで `callee.needs_dynamic_context` を引けるように、function table に metadata を持たせる。

```rust
struct DeclaredFunctionInfo {
    id: FuncId,
    needs_dynamic_context: bool,
}
```

---

## 6.5 MakeThunk が hidden context を snapshot する

`MakeThunk` lowering で、thunk runtime helper に current handler/guard stack を渡す。

現状の helper が仮にこうなら、

```rust
make_thunk(code, env_ptr)
```

こうする。

```rust
make_thunk(code, env_ptr, handler_stack, guard_stack)
```

Rust runtime 側の thunk object も同じ。

```rust
struct CpsThunkRuntime {
    code: i64,
    env: i64,
    handler_stack: i64,
    guard_stack: i64,
}
```

Cranelift helper:

```rust
extern "C" fn yulang_cps_make_thunk_i64(
    code: i64,
    env: i64,
    handler_stack: i64,
    guard_stack: i64,
) -> i64
```

---

## 6.6 ForceThunk は force-site context を渡す

`ForceThunk` helper も current handler/guard stack を受け取る。

```rust
extern "C" fn yulang_cps_force_thunk_i64(
    thunk: i64,
    force_handler_stack: i64,
    force_guard_stack: i64,
) -> i64
```

runtime helper 側では、まず暫定でこうする。

```rust
let handler_stack = if !is_empty_stack(force_handler_stack) {
    force_handler_stack
} else {
    thunk.handler_stack
};

let guard_stack = if !is_empty_stack(force_guard_stack) {
    force_guard_stack
} else {
    thunk.guard_stack
};
```

これで `each_list` が caller handler scope で force されたとき、caller handler が使われる。

---

# Milestone 6 の完成条件

以下を unignore して通す。

```rust
fn compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift()
```

この test は現在 ignored で、recursive `each_list` は caller の handler frame を function boundary 越しに渡す必要がある、とコメントされている。

成功条件:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift -- --nocapture
```

さらに、

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native once_finite_each -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_repr -- --nocapture
```

---

# Milestone 7: `std::undet.each` に戻す

Milestone 6 が通ったら、次は `std::undet.each`。
ただし `.once` はまだ標準の queue-backed once にしない。

## 7.1 まず local `once_dfs_int` + std `each`

テストを追加する。

```rust
#[test]
#[ignore = "Milestone 7: std::undet.each through local once_dfs"]
fn compares_std_each_with_local_once_dfs_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

my once_dfs_int(x: [std::undet::undet] int): int = catch x:
    std::undet::undet::branch (), k -> catch k true:
        std::undet::undet::reject (), _ -> k false
        v -> v
    std::undet::undet::reject (), _ -> 0
    v -> v

once_dfs_int { each [1, 2, 3] }
"#).expect("std each with local once_dfs");
    });
}
```

名前解決が違えば `undet::branch` / `branch` などに調整する。

## 7.2 ここで失敗しやすい理由

`std::undet.each` はこういう実装になっている。`fold` と `sub::return` を使う。

```yulang
pub each xs = sub::sub {
    xs.fold (): \() x -> if branch() { sub::return x } else ()
    reject()
}
```

なので必要になるものは、

```text
- fold callback
- lazy/function thunk callback
- sub::return handler
- branch inside callback
- direct call / closure call context propagation
```

Milestone 7 が失敗したら、まず見るのは `fold` callback が direct call なのか closure call なのか。
closure call なら `ApplyClosure` にも dynamic handler context を渡す必要がある。

---

# ApplyClosure にも dynamic context を渡す

Milestone 7 で `fold` が絡むと、closure callback が出る可能性が高い。

CPS eval 側はこう直す。

```rust
CpsStmt::ApplyClosure { dest, closure, arg } => {
    let closure = read_closure(function, &values, *closure)?;
    let arg = read_plain_value(function, &values, *arg)?;

    let result = eval_continuations(
        module,
        function,
        closure.entry,
        vec![CpsRuntimeValue::Plain(arg)],
        closure.values.as_ref().clone(),
        active_handlers.clone(),
        guard_stack.clone(),
    )?;

    write_value(&mut values, *dest, result);
}
```

Cranelift 側も、closure entry invocation に current handler/guard stack を渡す。
closure object に code/env だけでなく、必要なら creation-time handler envs を持たせる。
ただし最初は **force/call site context を優先** でよい。

---

# Milestone 8: queue-backed once

ここからが本当の `std::undet.once` だよ〜。
標準の `once` は queue に resumption `k` を保存する。`native-undet-plan.md` でも `std::undet.once` の hard cases として saved resumption queues と `list<resumption>` が挙がっている。

## 8.1 まずやってはいけないこと

```text
VmValue::List に CpsRuntimeValue::Resumption を無理やり入れる
```

これはやめる。

## 8.2 推奨: CPS runtime 専用 ControlList を作る

CPS interpreter 側では、まず `CpsRuntimeValue` に control list を足す。

```rust
enum CpsRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),

    ControlList(Rc<Vec<CpsRuntimeValue>>),
}
```

ただし `Vec<CpsRuntimeValue>` は clone が重いので、後で `Rc<VecDeque<_>>` や persistent list に変えてよい。

## 8.3 list primitive を CPSRuntimeValue 対応にする

今は primitive fallback が `runtime::vm::primitive::apply_primitive` に委譲されている。これは `VmValue` しか扱えない。最新コミットで list ops のために VM primitive へ委譲するようになっているけど、resumption list には使えない。

なので CPS 側 primitive eval を分ける。

```rust
fn eval_primitive_value(
    op: PrimitiveOp,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    match op {
        PrimitiveOp::ListEmpty => Ok(CpsRuntimeValue::ControlList(Rc::new(Vec::new()))),

        PrimitiveOp::ListSingleton => {
            let [value] = args.try_into().unwrap();
            Ok(CpsRuntimeValue::ControlList(Rc::new(vec![value])))
        }

        PrimitiveOp::ListMerge | PrimitiveOp::ListAppend => {
            let [left, right] = args.try_into().unwrap();
            merge_control_or_plain_lists(left, right)
        }

        PrimitiveOp::ListUncons => {
            let [list] = args.try_into().unwrap();
            uncons_control_or_plain_list(list)
        }

        _ => {
            let plain = args
                .into_iter()
                .map(into_plain_for_primitive)
                .collect::<Result<Vec<_>, _>>()?;
            runtime::vm::primitive::apply_primitive(op, &plain)
                .map(CpsRuntimeValue::Plain)
                .map_err(|_| CpsEvalError::UnsupportedPrimitive { op })
        }
    }
}
```

ここで `ListUncons` は `opt (head, tail)` を返す必要がある。
`head` が resumption の場合、`VmValue::Tuple` では表せない。
したがって `CpsRuntimeValue` 側にも tuple/variant を持たせるのが安全。

```rust
enum CpsRuntimeValue {
    ...
    Tuple(Vec<CpsRuntimeValue>),
    Variant {
        tag: core_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },
}
```

この変更は大きいけど、`std::undet.once` には必要。

## 8.4 Pattern binding を `VmValue` ではなく `CpsRuntimeValue` 対応にする

現在の pattern binding が `VmValue` 前提なら、queue-backed once で壊れる。
`std::opt::opt::just (k, queue)` の `k` が resumption、`queue` が control list だから。

必要な変更:

```rust
fn bind_pattern_runtime_value(
    pattern: &runtime::Pattern,
    value: CpsRuntimeValue,
) -> CpsEvalResult<Vec<(CpsValueId, CpsRuntimeValue)>> {
    match pattern {
        Pattern::Bind { ... } => ...
        Pattern::Tuple { items, .. } => {
            let CpsRuntimeValue::Tuple(values) = value else { ... };
            ...
        }
        Pattern::Variant { tag, value: pattern_value, .. } => {
            let CpsRuntimeValue::Variant { tag: actual, value } = value else { ... };
            ...
        }
        ...
    }
}
```

これが入ると、`std::undet.once` の queue がかなり現実になる。

---

# Milestone 8 の Cranelift 版

CPS eval / CPS repr eval で control list が通った後、Cranelift に行く。

Cranelift scalar runtime では、control list を opaque pointer として扱う。

```rust
#[repr(C)]
struct CpsControlList {
    items: Vec<i64>, // opaque handles: resumption/thunk/value pointers
}
```

helper:

```rust
#[no_mangle]
extern "C" fn yulang_cps_list_empty() -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_singleton(value: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_append(list: i64, value: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_merge(left: i64, right: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_uncons_is_nil(list: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_uncons_head(list: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_list_uncons_tail(list: i64) -> i64;
```

`ListUncons` を `opt` object として返すより、まずは match lowering 側で helper を呼ぶ方が簡単。

つまり、CPS repr Cranelift で

```yulang
case std::list::uncons queue:
    nil -> ...
    just (k, queue) -> ...
```

に相当する IR を見たら、

```text
if yulang_cps_list_uncons_is_nil(queue):
    nil arm
else:
    k = yulang_cps_list_uncons_head(queue)
    queue2 = yulang_cps_list_uncons_tail(queue)
    just arm
```

に落とす。

これは std special-case に見えるけど、CPS runtime の control-list lane に限定するなら許容できる。

---

# Milestone 9: `std::undet.once` scalar-unwrapped

ここで初めてこれを unignore する。

```rust
#[test]
#[ignore = "Milestone 9: std::undet.once with scalar unwrap"]
fn compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#).expect("std undet once scalar unwrap");
    });
}
```

ここで root は `int` に潰す。
`opt` を print しようとしない。

---

# Milestone 10: non-scalar CPS return / print

最後にやる。

```yulang
(each [1, 2, 3]).once
```

をそのまま native executable が print できるようにする。
これは `opt int` の print が必要なので、CPS executable 側の `OpaqueI64` を Yulang value として print できる必要がある。

ここは今すぐ触らない。

---

# 別LLへの具体指示

このまま渡していいよ〜。

```text
現在の状態:
- each_head は通った。
- recursive each_list が ignored regression として残っている。
- native-undet-plan.md では、recursive helpers like each_list are not inlined and still emit Perform without a known handler entry と整理されている。
- まず Milestone 6 だけを通す。

絶対にやらないこと:
- std::undet.once を直接触らない。
- value backend に resumption/thunk/handler を入れない。
- VmValue::List に Resumption を入れない。
- Cranelift から先に直さない。

やること:
1. source.rs の compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift を debug 用にコピーして、CPS eval / CPS repr eval / Cranelift の3段階に分ける。
2. CPS eval の DirectCall が active_handlers / guard_stack を callee に渡すようにする。
3. CPS eval の ForceThunk が force-site active handler stack を使えるようにする。
4. 同じ変更を cps_repr.rs に入れる。
5. ここまでで CPS eval / CPS repr eval が VM と一致することを確認する。
6. cps_repr_cranelift.rs で effectful / thunk-returning function に hidden handler_stack / guard_stack context を渡す。
7. DirectCall lowering で callee が context を必要とする場合、current handler_stack / guard_stack を hidden args として渡す。
8. MakeThunk helper に current handler_stack / guard_stack を渡して snapshot する。
9. ForceThunk helper に force-site handler_stack / guard_stack を渡す。
10. each_list ignored regression を unignore する。

成功条件:
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift -- --nocapture

次に進む条件:
- each_list が通ったら、std::undet.each + local once_dfs を試す。
- std::undet.once はまだ queue-backed once の設計が必要なので、いきなり触らない。
```

---

# りなの結論

Milestone 6 以降が失敗している原因は、もう「undet が難しい」ではなくて、かなり具体的に

> **recursive / non-inlined function call が dynamic handler context を失う**

に絞れているよ〜。

だから次に書くべきコードは、`std::undet` 本体ではなく、

```text
DirectCall / ApplyClosure / MakeThunk / ForceThunk に
active handler stack と guard stack を渡すコード
```

だねぇ。

`each_list` が通れば、次は `std::undet.each`。
`std::undet.once` はそのさらに後で、そこで初めて `list<resumption>` / control queue の設計に入るのが安全だと思うよ〜。
