うん、前提を **「継続もクロージャも第一級」** に置くなら、計画はかなり明確に変わるよ〜。
そして、いまの LLM の進捗報告は GitHub の最新コミット内容と一致してる。最新コミットでも、`std::undet.each + local once_dfs` は **CPS eval / CPS repr eval では VM と一致**、ただし **Cranelift は handler-arm abort を runtime helpers がまだ伝播していないため wrong scalar** と書かれているねぇ。

なので、今の状況からはこう見るのがよさそう。

```text
意味論:
  CPS eval      OK
  CPS repr eval OK

Cranelift:
  handler arm abort / non-local return の伝播が未実装
  -> reject path まで実行されて 0 になる
```

つまり次にやるべき最短修正は、**第一級値ドメインの大改造ではなく、まず Cranelift runtime に Aborted propagation を入れること**。
その後に、`std::undet.once` のための **第一級 resumption / closure / container 統合** に進むのが安全だと思うよ〜。

---

# 0. 現在地の正確な読み

## 完了していること

`native-undet-plan.md` では、recursive `each_list(xs): [choice] int` は caller の handler frame に届くようになり、`InstallHandler` / `UninstallHandler` と runtime handler stack により Milestone 6 は完了扱いになっている。

今の open は次の3つ。

```text
- std::undet.each は fold / sub::return / closure callback を使う
- std::undet.once には resumption queue が必要
- generated CPS executable は non-scalar Yulang values をまだ print できない
```

これも `native-undet-plan.md` の現状と一致している。

## 最新の失敗

最新コミットでは、handler arm body の return を `Aborted(value)` として CPS eval / CPS repr eval では伝播させている。`DirectCall`, `ApplyClosure`, `ForceThunk`, `Resume`, `ResumeWithHandler` が `Aborted` を上へ返し、root で unwrap する形になっている。けれど Cranelift では runtime helpers がまだ handler-arm abort を伝播できていない、と明記されている。

つまり、Cranelift で `0` になるのはかなり自然。
`sub::return` 相当の handler arm が「非局所 return」にならず、その後の `reject()` まで進んでしまっている可能性が高い。

---

# 1. 新しい全体方針

第一級継続・第一級クロージャを前提にするなら、方針はこれ。

```text
Phase A:
  Cranelift に Aborted propagation を実装して、Milestone 7 を JIT まで通す。

Phase B:
  CPS runtime の値ドメインを統一し、resumption / closure / thunk が
  list / tuple / variant / function argument を通れるようにする。

Phase C:
  std::undet.once の queue を、専用 ContinuationArray ではなく
  first-class CpsValue container として実装する。

Phase D:
  std::undet.once scalar-unwrapped を通す。

Phase E:
  non-scalar return / print / .list / .logic へ進む。
```

ここで大事なのは、**継続用の専用配列ではなく、CPS runtime の値コンテナを作る** ことだねぇ。

`std::undet.once` は実際に `k` を queue に保存し、`uncons` で取り出して `k false` している。
だから `k` は普通の値のように list / tuple / variant を通れる必要がある。

---

# 2. Phase A: Cranelift に `Aborted` propagation を入れる

## 目的

CPS eval / CPS repr eval では通っている `std::undet.each + local once_dfs` を、Cranelift JIT でも通す。

今の症状:

```text
VM: 1
CPS eval: 1
CPS repr eval: 1
Cranelift: 0
```

これは handler arm abort が compiled runtime で伝播されず、`reject` path に流れている。

---

## 2.1 `cps_runtime.rs` に abort TLS を追加する

今の Cranelift runtime は handler stack / guard stack / thunk / closure / resumption を thread-local に持っている。`cps_runtime.rs` にはすでに `YULANG_CPS_I64_HANDLER_STACK`, `YULANG_CPS_I64_GUARD_STACK`, thunk registry などがある。

そこに abort state を足す。

```rust
thread_local! {
    static YULANG_CPS_I64_ABORT: RefCell<Option<i64>> =
        const { RefCell::new(None) };
}
```

追加する helper:

```rust
#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_abort_i64(value: i64) -> i64 {
    YULANG_CPS_I64_ABORT.with(|slot| {
        *slot.borrow_mut() = Some(value);
    });
    value
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_abort_active_i64() -> i64 {
    YULANG_CPS_I64_ABORT.with(|slot| i64::from(slot.borrow().is_some()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_abort_value_i64() -> i64 {
    YULANG_CPS_I64_ABORT.with(|slot| slot.borrow().unwrap_or(0))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_clear_abort_i64() -> i64 {
    YULANG_CPS_I64_ABORT.with(|slot| {
        *slot.borrow_mut() = None;
    });
    0
}
```

あると便利な helper:

```rust
#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_abort_value_or_i64(value: i64) -> i64 {
    YULANG_CPS_I64_ABORT.with(|slot| slot.borrow().unwrap_or(value))
}
```

ただし、non-tail call の後は「値を差し替える」だけでは足りない。
残りの statement を実行せず **return** する必要があるので、Cranelift 側では branch が必要。

---

## 2.2 Cranelift lowering に `return_if_abort_active` を作る

`cps_repr_cranelift.rs` に共通 helper を作る。

擬似コード:

```rust
fn return_if_abort_active(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
) -> CpsReprCraneliftResult<()> {
    let active_fn = declare_import(
        jit,
        builder,
        "yulang_cps_abort_active_i64",
        &[],
        types::I64,
    )?;
    let value_fn = declare_import(
        jit,
        builder,
        "yulang_cps_abort_value_i64",
        &[],
        types::I64,
    )?;

    let active_call = builder.ins().call(active_fn, &[]);
    let active = builder.inst_results(active_call)[0];

    let is_active = builder.ins().icmp_imm(
        cranelift_codegen::ir::condcodes::IntCC::NotEqual,
        active,
        0,
    );

    let abort_block = builder.create_block();
    let cont_block = builder.create_block();

    builder.ins().brif(is_active, abort_block, &[], cont_block, &[]);

    builder.switch_to_block(abort_block);
    let value_call = builder.ins().call(value_fn, &[]);
    let value = builder.inst_results(value_call)[0];
    builder.ins().return_(&[value]);

    builder.switch_to_block(cont_block);
    Ok(())
}
```

これを **内部 call の直後** に入れる。

対象:

```text
DirectCall
ApplyClosure
ForceThunk
Resume
ResumeWithHandler
call_continuation
Perform handler-entry call
```

CPS eval / repr eval の `Aborted` propagation と同じ場所だねぇ。最新コミットで evaluator 側はここを直している。

---

## 2.3 `Perform` の handler arm return を abort に包む

CPS eval / repr eval では、`Perform` で handler arm body を評価した結果を `Aborted(value)` に包んで返している。

Cranelift では、`CpsTerminator::Perform` の handler entry call 後に abort flag を立てる。

擬似コード:

```rust
// result = handler_entry(payload, resumption)
let result = call_handler_entry(...);

// if no abort is already active, mark this handler arm result as abort
let active = call_abort_active();
if active == 0 {
    call yulang_cps_abort_i64(result);
}

return result;
```

Cranelift の branch で書くなら:

```rust
let active = call_abort_active(...);
let is_active = active != 0;

let already_block = builder.create_block();
let mark_block = builder.create_block();

builder.ins().brif(is_active, already_block, &[], mark_block, &[]);

builder.switch_to_block(mark_block);
call yulang_cps_abort_i64(result);
builder.ins().return_(&[result]);

builder.switch_to_block(already_block);
builder.ins().return_(&[result]);
```

もし handler arm の中ですでに nested abort が起きているなら、それを上書きしない。

---

## 2.4 root 実行の前後で abort state を clear する

内部 function boundary で clear してはいけない。
そうすると abort が途中で止まる。

root 実行の前後だけ clear する。

`CpsReprJitModule::run_roots_i64` 相当で、

```rust
yulang_cps_clear_abort_i64();
let value = root();
yulang_cps_clear_abort_i64();
```

object/exe harness でも root ごとに clear する。
複数 root 実行時に abort が漏れないようにするため。

---

## 2.5 JIT / object の symbol import を追加

JIT builder に追加:

```rust
builder.symbol("yulang_cps_abort_i64", yulang_cps_abort_i64 as *const u8);
builder.symbol("yulang_cps_abort_active_i64", yulang_cps_abort_active_i64 as *const u8);
builder.symbol("yulang_cps_abort_value_i64", yulang_cps_abort_value_i64 as *const u8);
builder.symbol("yulang_cps_clear_abort_i64", yulang_cps_clear_abort_i64 as *const u8);
```

object backend 側でも import 宣言を追加。

---

## 2.6 Phase A の成功条件

まず ignored の Milestone 7 debug test を通す。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_std_each_with_local_once_dfs_eval_layers -- --nocapture
```

そして non-debug regression も通す。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_std_each_with_local_once_dfs_through_cps_repr_cranelift -- --nocapture
```

期待:

```text
VM: 1
CPS eval: 1
CPS repr eval: 1
Cranelift: 1
```

ここが通るまで、`std::undet.once` の queue には進まない。

---

# 3. Phase B: 継続・クロージャ・thunk を第一級 CPS value にする

Phase A が通ったら、第一級化に入る。

## 3.1 目的

`k` や closure が以下を通れるようにする。

```text
- local binding
- function argument
- closure argument
- tuple
- list
- variant
- pattern match / case
- later resume/apply
```

標準 `std::undet.once` は queue に `k` を入れるので、これは必須。

---

## 3.2 CPS evaluator の `CpsRuntimeValue` を統一する

方向:

```rust
#[derive(Debug, Clone, PartialEq)]
enum CpsRuntimeValue {
    Plain(runtime::VmValue),

    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),

    List(Rc<Vec<CpsRuntimeValue>>),
    Tuple(Vec<CpsRuntimeValue>),
    Variant {
        tag: core_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },

    Aborted(Box<CpsRuntimeValue>),
}
```

`Aborted` は最新コミットですでに evaluator 側へ入っている。
ここに `List/Tuple/Variant` を「`VmValue` ではなく `CpsRuntimeValue` を格納する形」で入れる。

---

## 3.3 plain 変換 helper を用意する

VM と比較するため、plain に戻せるものだけ戻す。

```rust
fn cps_value_from_vm(value: runtime::VmValue) -> CpsRuntimeValue {
    match value {
        runtime::VmValue::Tuple(items) => {
            CpsRuntimeValue::Tuple(
                items.into_iter().map(cps_value_from_vm).collect(),
            )
        }
        runtime::VmValue::Variant { tag, value } => {
            CpsRuntimeValue::Variant {
                tag,
                value: value.map(|v| Box::new(cps_value_from_vm(*v))),
            }
        }
        runtime::VmValue::List(list) => {
            let items = list
                .to_vec()
                .into_iter()
                .map(|item| cps_value_from_vm(item.as_ref().clone()))
                .collect::<Vec<_>>();
            CpsRuntimeValue::List(Rc::new(items))
        }
        other => CpsRuntimeValue::Plain(other),
    }
}

fn cps_value_to_vm(value: CpsRuntimeValue) -> Option<runtime::VmValue> {
    match value {
        CpsRuntimeValue::Plain(value) => Some(value),

        CpsRuntimeValue::Tuple(items) => {
            Some(runtime::VmValue::Tuple(
                items.into_iter()
                    .map(cps_value_to_vm)
                    .collect::<Option<Vec<_>>>()?,
            ))
        }

        CpsRuntimeValue::Variant { tag, value } => {
            Some(runtime::VmValue::Variant {
                tag,
                value: value
                    .map(|value| cps_value_to_vm(*value).map(Box::new))
                    .transpose()?,
            })
        }

        CpsRuntimeValue::List(items) => {
            let vm_items = items
                .iter()
                .cloned()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()?;

            // 既存 ListTree constructor に合わせて実装
            Some(runtime::VmValue::List(list_tree_from_vm_values(vm_items)))
        }

        CpsRuntimeValue::Aborted(value) => cps_value_to_vm(*value),

        CpsRuntimeValue::Resumption(_)
        | CpsRuntimeValue::Thunk(_)
        | CpsRuntimeValue::Closure(_) => None,
    }
}
```

root が scalar の間は、`Resumption` / `Closure` が root に出たら error でよい。

---

## 3.4 DirectCall / ApplyClosure の引数を plain 限定から外す

これはもう一部進んでいる。最新コミットでも evaluator 側では `DirectCall` の args を `read_plain_value` ではなく `read_value` に寄せている。

同じことを徹底する。

対象:

```text
DirectCall
ApplyClosure
Resume
ResumeWithHandler
ForceThunk
Primitive
```

ただし primitive は op によって plain 変換できるものと control value 対応が必要なものを分ける。

---

# 4. Phase C: list / tuple / variant primitive を CPS value 対応にする

## 4.1 なぜ必要か

`std::undet.once` は以下を行う。

```yulang
std::list::append queue [k]
std::list::uncons queue
std::opt::opt::just (k, queue) -> loop(k false, queue)
```

ここで `k` は `Resumption`。
だから `list` / `tuple` / `variant` が `CpsRuntimeValue` を格納できないと壊れる。

---

## 4.2 CPS eval primitive

`runtime::vm::primitive::apply_primitive` への fallback は `VmValue` にしか効かない。`each_head` では役に立ったが、`list<resumption>` では足りない。最新コミットで primitive fallback が入ったこと自体は良いが、次の段階では CPS value 対応が必要になる。

実装方針:

```rust
fn eval_cps_primitive(
    op: core_ir::PrimitiveOp,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    match op {
        core_ir::PrimitiveOp::ListEmpty => {
            Ok(CpsRuntimeValue::List(Rc::new(Vec::new())))
        }

        core_ir::PrimitiveOp::ListSingleton => {
            let value = expect_one(args)?;
            Ok(CpsRuntimeValue::List(Rc::new(vec![value])))
        }

        core_ir::PrimitiveOp::ListMerge => {
            let (left, right) = expect_two(args)?;
            merge_cps_lists(left, right)
        }

        core_ir::PrimitiveOp::ListAppend => {
            let (list, value) = expect_two(args)?;
            append_cps_list(list, value)
        }

        core_ir::PrimitiveOp::ListUncons => {
            let list = expect_one(args)?;
            uncons_cps_list_as_opt(list)
        }

        core_ir::PrimitiveOp::ListLen => {
            let list = expect_one(args)?;
            list_len_cps(list)
        }

        core_ir::PrimitiveOp::ListIndex => {
            let (list, index) = expect_two(args)?;
            list_index_cps(list, index)
        }

        _ => {
            let vm_args = args
                .into_iter()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()
                .ok_or(CpsEvalError::UnsupportedPrimitive { op })?;

            runtime::vm::primitive::apply_primitive(op, &vm_args)
                .map(cps_value_from_vm)
                .map_err(|_| CpsEvalError::UnsupportedPrimitive { op })
        }
    }
}
```

---

## 4.3 `uncons` の返り値

`uncons` は `opt (head, tail)` を返す必要がある。
`head` が resumption の場合、`VmValue::Variant` ではなく `CpsRuntimeValue::Variant` で返す。

```rust
fn uncons_cps_list_as_opt(value: CpsRuntimeValue) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::List(items) = value else {
        return Err(CpsEvalError::ExpectedList);
    };

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
        value: Some(Box::new(CpsRuntimeValue::Tuple(vec![head, tail]))),
    })
}
```

タグ名は既存の `std::opt::opt::nil` / `just` と比較される形に合わせる。
もし `VariantTagEq` が name だけでなく path hash を見ているなら、同じ tag encoding を使う。

---

## 4.4 `TupleGet` / `VariantTagEq` / `VariantPayload`

これらが `VmValue` だけを見る実装だと、`just (k, queue)` が壊れる。

修正例:

```rust
CpsStmt::TupleGet { dest, tuple, index } => {
    let value = match read_value(function, &values, *tuple)? {
        CpsRuntimeValue::Tuple(items) => {
            items.get(*index)
                .cloned()
                .ok_or(CpsEvalError::TupleIndexOutOfRange)?
        }

        CpsRuntimeValue::Plain(runtime::VmValue::Tuple(items)) => {
            cps_value_from_vm(
                items.get(*index)
                    .cloned()
                    .ok_or(CpsEvalError::TupleIndexOutOfRange)?
            )
        }

        other => return Err(CpsEvalError::ExpectedTuple { value: other }),
    };

    write_value(&mut values, *dest, value);
}
```

```rust
CpsStmt::VariantTagEq { dest, variant, tag } => {
    let ok = match read_value(function, &values, *variant)? {
        CpsRuntimeValue::Variant { tag: actual, .. } => actual == *tag,

        CpsRuntimeValue::Plain(runtime::VmValue::Variant { tag: actual, .. }) => {
            actual == *tag
        }

        _ => false,
    };

    write_value(
        &mut values,
        *dest,
        CpsRuntimeValue::Plain(runtime::VmValue::Bool(ok)),
    );
}
```

```rust
CpsStmt::VariantPayload { dest, variant } => {
    let value = match read_value(function, &values, *variant)? {
        CpsRuntimeValue::Variant { value: Some(value), .. } => *value,
        CpsRuntimeValue::Variant { value: None, .. } => {
            CpsRuntimeValue::Plain(runtime::VmValue::Unit)
        }

        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
            value: Some(value), ..
        }) => cps_value_from_vm(*value),

        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
            value: None, ..
        }) => CpsRuntimeValue::Plain(runtime::VmValue::Unit),

        other => return Err(CpsEvalError::ExpectedVariant { value: other }),
    };

    write_value(&mut values, *dest, value);
}
```

同じ修正を CPS repr eval にも入れる。

---

# 5. Phase D: First-class resumption / closure tests

`std::undet.once` に行く前に、小さい第一級性テストを入れる。

## 5.1 resumption in tuple

```rust
#[test]
#[ignore = "first-class resumption in tuple"]
fn compares_resumption_stored_in_tuple_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        my pair = (k, 0)
        case pair:
            (r, _) -> if r true: 1 else: 2
    v -> if v: 10 else: 20
"#).expect("resumption tuple");
    });
}
```

## 5.2 resumption in list

```rust
#[test]
#[ignore = "first-class resumption in list"]
fn compares_resumption_stored_in_list_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        case std::list::uncons [k]:
            std::opt::opt::nil -> 0
            std::opt::opt::just (r, _) ->
                if r true: 1 else: 2
    v -> if v: 10 else: 20
"#).expect("resumption list");
    });
}
```

## 5.3 closure in tuple

```rust
#[test]
#[ignore = "first-class closure in tuple"]
fn compares_closure_stored_in_tuple_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
my apply_pair p = case p:
    (f, x) -> f x

apply_pair(\x -> x + 1, 41)
"#).expect("closure tuple");
    });
}
```

## 5.4 closure in list

```rust
#[test]
#[ignore = "first-class closure in list"]
fn compares_closure_stored_in_list_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
case std::list::uncons [\x -> x + 1]:
    std::opt::opt::nil -> 0
    std::opt::opt::just (f, _) -> f 41
"#).expect("closure list");
    });
}
```

この4つが通れば、「継続もクロージャも第一級」と言いやすくなる。

---

# 6. Phase E: Cranelift の value container は `ControlPtr`

今の `cps_runtime.rs` には、すでに `YulangCpsI64HeapValue::Tuple`, `Variant`, `List(Vec<i64>)` がある。
これは方向としては悪くない。`Vec<i64>` に resumption pointer / closure pointer / thunk pointer / runtime heap value pointer を入れられるなら、**第一級 CPS value container** として使える。

ただし、名前や invariant をはっきりさせるべき。

## 6.1 これは OK

```rust
enum YulangCpsI64HeapValue {
    Tuple(Box<[i64]>),
    Variant { tag: i64, value: Option<i64> },
    List(Vec<i64>),
}
```

この `i64` が opaque CPS value handle なら OK。
つまり中身は以下を全部許す。

```text
ScalarI64
RuntimeValuePtr
ResumptionPtr
ThunkPtr
ClosurePtr
HeapValuePtr
```

## 6.2 これは NG

```text
List(Vec<i64>) だが実際は scalar/runtime heap value だけ想定
ResumptionPtr を入れると print / tag / primitive が壊れる
```

なので doc comment を足すといい。

```rust
/// Heap/container value used by the CPS scalar runtime.
/// The contained i64 values are opaque CPS value handles:
/// scalar values, runtime-value pointers, resumptions, thunks, closures,
/// and other heap containers may all flow here.
enum YulangCpsI64HeapValue { ... }
```

---

## 6.3 Cranelift に必要な helper

今ある tuple/list/variant helper に加えて、`std::undet.once` 用には最低限これが必要。

```rust
#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_append_i64(list: i64, value: i64) -> i64;

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_uncons_i64(list: i64) -> i64;
```

`uncons` は `std::opt::opt` の variant を返す。
Cranelift 側の `VariantTagEq` / `VariantPayload` / `TupleGet` がこれを読めるようにする。

もし既存 primitive lowering が `ListUncons` を直接 `yulang_cps_list_uncons_i64` に落とせるならそれでよい。

---

# 7. Phase F: `std::undet.once` scalar-unwrapped

ここで初めて標準 `.once` に戻る。

```rust
#[test]
#[ignore = "std::undet.once scalar-unwrapped"]
fn compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#).expect("std undet once scalar unwrapped");
    });
}
```

root は `int`。
`opt` をそのまま native executable で print するのはまだ後回し。

---

# 8. 作業順のまとめ

別LLに渡すなら、この順番にしてねぇ。

```text
1. Cranelift abort propagation を入れる
   - cps_runtime.rs に abort TLS
   - Perform handler result で abort set
   - DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler 後に abort check
   - root 実行前後で clear

2. Milestone 7 を Cranelift まで通す
   - std::undet.each + local once_dfs
   - VM/CPS/CPS repr/Cranelift が全部 1

3. CPS eval / CPS repr eval の CpsRuntimeValue を統一
   - Resumption / Thunk / Closure / List / Tuple / Variant / Aborted

4. DirectCall / ApplyClosure args を CpsRuntimeValue にする
   - plain 限定を外す

5. list/tuple/variant primitive を CpsRuntimeValue 対応にする
   - ListSingleton に resumption / closure が入る
   - ListUncons が Control Variant を返す

6. first-class tests を追加
   - resumption in tuple
   - resumption in list
   - closure in tuple
   - closure in list

7. Cranelift の Tuple/List/Variant を ControlPtr として扱う
   - Vec<i64> は opaque CPS value handles
   - ResumptionPtr / ClosurePtr / ThunkPtr を入れてよい

8. std::undet.once scalar-unwrapped
   - case once: nil -> 0; just x -> x
```

---

# 9. 今回の計画で前回から変わった点

前回の計画では、queue-backed once のために「CPS opaque queue helper」を作る話が中心だった。
でも、継続もクロージャも第一級にするなら、それでは狭すぎる。

新計画では、

```text
queue helper
```

ではなく、

```text
CPS runtime の統一 value container
```

を作る。

`std::undet.once` は queue に `k` を入れるだけでなく、`just (k, queue)` という tuple/variant pattern で取り出す。
だから list だけではなく tuple / variant / pattern / function args まで、CPS value 全体で扱える必要がある。

---

# 10. りなの判断

今すぐの blocker は **Cranelift abort propagation**。
これは最新コミットのメッセージにも、そのまま「remaining piece」として書かれている。

その次が、あなたの言う通り **継続とクロージャの第一級化**。
これは「専用 queue」ではなく、

```text
CpsRuntimeValue / CpsReprRuntimeValue / Cranelift ControlPtr
```

として値ドメインを広げる方向がいい。

だから、次に別LLへ渡すならこう言うのが一番よさそう。

```text
まず Cranelift の Aborted propagation を直して Milestone 7 を通す。
その後、std::undet.once 用の専用 queue ではなく、
CPS runtime の統一値ドメインを作る。
Resumption / Closure / Thunk が List / Tuple / Variant / function arg を
普通に通れるようにする。
```

この順番なら、今の進捗を壊さず、`std::undet.once` にちゃんと向かえると思うよ〜。
