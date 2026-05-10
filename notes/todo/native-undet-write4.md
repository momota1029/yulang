うん、**変更は出る** と思う。
前の計画は「queue-backed once のために CPS opaque queue を作る」くらいの書き方だったけど、あなたの言っている「第一級 = 内部でも値として扱えること」を採用するなら、もっとはっきり **CPS runtime の値ドメインを統合する計画** に変えたほうがいいねぇ。

いまの `native-undet-plan.md` では、Milestone 6 の recursive `each_list` は handler stack threading で通った扱いになっていて、次は `std::undet::each` と local DFS once、さらにその後 `std::undet.once` の resumption queue が open になっている。
そして実際の `std::undet.once` / `logic` は、`k` を queue に入れて、あとで `std::list::uncons queue` で取り出し、`k false` する構造になっている。

つまり、ここからは **resumption が list / tuple / variant / function arg を普通に通れる** 必要がある。

---

# 新しい実装計画: First-class CPS Value Domain 版

## 大方針

前の計画から変える点はこれ。

```text
旧:
  std::undet.once 用に opaque queue helper を作る

新:
  CPS runtime 内に、resumption / thunk / closure / list / tuple / variant を含む
  統一された CpsValue domain を作る
```

ここでいう「統一」は、`VmValue` と完全に同じ Rust 型・同じ machine layout にするという意味ではない。
でも **CPS runtime の中では全部 “値” として扱える** ようにする。

つまり、

```rust
list<resumption>
tuple(resumption, queue)
variant just(tuple(resumption, queue))
function_arg(queue)
```

が全部通るようにする。

---

# 0. 絶対に避けること

別LLに渡すなら、まずこれを強く書くのがいいよ〜。

```text
禁止:
- std::undet.once 専用の ContinuationArray を作る
- ContinuationTuple のような専用構造だけで queue を実装する
- VmValue::List に ResumptionPtr を雑に入れる
- ResumptionPtr を RuntimeValuePtr と同一視する
- list(k) / append queue [k] だけを special-case する
- Cranelift 側だけを直して CPS eval / CPS repr eval を放置する
```

必要なのは **専用 queue** ではなく、**CPS runtime value としての resumption**。

---

# 1. 新しい Milestone 構成

## Milestone 7: `std::undet.each` + local DFS once

これは今の `native-undet-plan.md` の次段階と同じ。
ただし目的を明確にする。

### 目的

`std::undet.each` が使う

* `fold`
* `sub::return`
* closure callback
* dynamic handler context forwarding

を通す。

### テスト

```rust
#[test]
#[ignore = "Milestone 7: std::undet.each with local DFS once"]
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

### 失敗したら見る場所

`std::undet.each` は `fold` と `sub::return` を使うので、主にここを見る。

```text
- ApplyClosure が active_handlers / guard_stack を落としていないか
- fold callback closure に dynamic context が渡っているか
- sub::return が handler stack で見つかっているか
- ForceThunk が force-site handler stack を優先しているか
```

### 実際に書くべきコード

`CpsStmt::ApplyClosure` が、caller の context を closure body に渡すようにする。

```rust
CpsStmt::ApplyClosure { dest, closure, arg } => {
    let closure = read_closure(function, &values, *closure)?;
    let arg = read_value(function, &values, *arg)?;

    let result = eval_continuations(
        module,
        function,
        closure.entry,
        vec![arg],
        closure.values.as_ref().clone(),
        active_handlers.clone(),
        guard_stack.clone(),
    )?;

    write_value(&mut values, *dest, result);
}
```

ここで `arg` は `read_plain_value` ではなく、できれば `read_value` に寄せる。
今後、closure に queue や resumption を渡す必要が出るから。

---

# 2. Milestone 8A: CPS evaluator の値ドメイン統合

ここが新しく必要になる。

## 目的

CPS evaluator 内で、resumption / thunk / closure / tuple / list / variant を同じ値ドメインで扱う。

## 実装する型

`cps_eval.rs` の `CpsRuntimeValue` をこういう方向にする。

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
}
```

ポイントは、`List` / `Tuple` / `Variant` が `runtime::VmValue` ではなく **`CpsRuntimeValue` を格納すること**。

これで、

```text
[k]
(k, queue)
just (k, queue)
```

が表せる。

## 変換 helper

既存の `VmValue` ベース処理を壊さないために、変換関数を作る。

```rust
fn cps_value_from_vm(value: runtime::VmValue) -> CpsRuntimeValue {
    match value {
        runtime::VmValue::List(list) => {
            let items = list
                .to_vec()
                .into_iter()
                .map(|item| cps_value_from_vm(item.as_ref().clone()))
                .collect::<Vec<_>>();
            CpsRuntimeValue::List(Rc::new(items))
        }
        runtime::VmValue::Tuple(items) => {
            CpsRuntimeValue::Tuple(
                items.into_iter().map(cps_value_from_vm).collect()
            )
        }
        runtime::VmValue::Variant { tag, value } => {
            CpsRuntimeValue::Variant {
                tag,
                value: value.map(|v| Box::new(cps_value_from_vm(*v))),
            }
        }
        other => CpsRuntimeValue::Plain(other),
    }
}

fn cps_value_to_vm(value: CpsRuntimeValue) -> Option<runtime::VmValue> {
    match value {
        CpsRuntimeValue::Plain(value) => Some(value),

        CpsRuntimeValue::List(items) => {
            let vm_items = items
                .iter()
                .cloned()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()?;

            Some(runtime::VmValue::List(
                runtime::runtime::list_tree::ListTree::from_vec(
                    vm_items.into_iter().map(Rc::new).collect()
                )
            ))
        }

        CpsRuntimeValue::Tuple(items) => {
            let vm_items = items
                .into_iter()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()?;

            Some(runtime::VmValue::Tuple(vm_items))
        }

        CpsRuntimeValue::Variant { tag, value } => {
            Some(runtime::VmValue::Variant {
                tag,
                value: value
                    .map(|v| cps_value_to_vm(*v).map(Box::new))
                    .transpose()?,
            })
        }

        CpsRuntimeValue::Resumption(_)
        | CpsRuntimeValue::Thunk(_)
        | CpsRuntimeValue::Closure(_) => None,
    }
}
```

`ListTree::from_vec` がなければ、既存の constructor に合わせて実装する。

---

# 3. Milestone 8B: primitive eval を CpsRuntimeValue 対応にする

今の `each_head` では、未対応 primitive を `runtime::vm::primitive::apply_primitive` に委譲することで進んだ。これは list ops には有効だったけど、`list<resumption>` には足りない。`apply_primitive` は `VmValue` しか扱えないからねぇ。

## 実装する関数

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
            let [value] = one_arg(args)?;
            Ok(CpsRuntimeValue::List(Rc::new(vec![value])))
        }

        core_ir::PrimitiveOp::ListMerge => {
            let (left, right) = two_args(args)?;
            merge_cps_lists(left, right)
        }

        core_ir::PrimitiveOp::ListAppend => {
            let (list, value) = two_args(args)?;
            append_cps_list(list, value)
        }

        core_ir::PrimitiveOp::ListUncons => {
            let [list] = one_arg(args)?;
            uncons_cps_list_as_opt(list)
        }

        core_ir::PrimitiveOp::ListLen => {
            let [list] = one_arg(args)?;
            list_len_cps(list)
        }

        core_ir::PrimitiveOp::ListIndex => {
            let (list, index) = two_args(args)?;
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

## list helpers

```rust
fn merge_cps_lists(
    left: CpsRuntimeValue,
    right: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::List(left) = left else {
        return Err(CpsEvalError::ExpectedList);
    };
    let CpsRuntimeValue::List(right) = right else {
        return Err(CpsEvalError::ExpectedList);
    };

    let mut items = left.as_ref().clone();
    items.extend(right.iter().cloned());
    Ok(CpsRuntimeValue::List(Rc::new(items)))
}

fn append_cps_list(
    list: CpsRuntimeValue,
    value: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::List(list) = list else {
        return Err(CpsEvalError::ExpectedList);
    };

    let mut items = list.as_ref().clone();
    items.push(value);
    Ok(CpsRuntimeValue::List(Rc::new(items)))
}
```

## uncons が大事

`std::undet.once` はここを使う。

```yulang
case std::list::uncons queue:
    std::opt::opt::nil -> ...
    std::opt::opt::just (k, queue) -> loop(k false, queue)
```

なので `uncons` は `CpsRuntimeValue::Variant` を返す。

```rust
fn uncons_cps_list_as_opt(
    list: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::List(items) = list else {
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
        value: Some(Box::new(CpsRuntimeValue::Tuple(vec![
            head,
            tail,
        ]))),
    })
}
```

タグ名が実際には canonical path に依存するなら、既存の VM `ListUncons` が返す tag と同じ `Name` を使う。
ここは実装中に必ず確認する。

---

# 4. Milestone 8C: `TupleGet` / `VariantTagEq` / `VariantPayload` を CpsRuntimeValue 対応にする

今の CPS lowering は match を `VariantTagEq` / `VariantPayload` / `TupleGet` へ落としている可能性が高い。
この3つが `VmValue` しか見ないと、`just (k, queue)` が壊れる。

## 書くべきコード

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
    let matches = match read_value(function, &values, *variant)? {
        CpsRuntimeValue::Variant { tag: actual, .. } => actual == *tag,

        CpsRuntimeValue::Plain(runtime::VmValue::Variant { tag: actual, .. }) => {
            actual == *tag
        }

        _ => false,
    };

    write_value(
        &mut values,
        *dest,
        CpsRuntimeValue::Plain(runtime::VmValue::Bool(matches)),
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

これで `just (k, queue)` の destructuring ができる。

---

# 5. Milestone 8D: DirectCall / ApplyClosure の引数を plain 限定から外す

これも重要。
`std::undet.once` の recursive loop は `queue` を引数として渡す。

```yulang
loop(k false, queue)
```

この `queue` は `list<resumption>`。
だから DirectCall が `read_plain_value` しか使えないと詰む。

## 書くべき変更

### 旧

```rust
let args = args
    .iter()
    .map(|id| read_plain_value(function, &values, *id))
    .collect::<CpsEvalResult<Vec<_>>>()?;

let result = eval_function(..., args)?;
```

### 新

```rust
let args = args
    .iter()
    .map(|id| read_value(function, &values, *id))
    .collect::<CpsEvalResult<Vec<_>>>()?;

let result = eval_function_with_cps_values(
    module,
    target_function,
    args,
    active_handlers.clone(),
    guard_stack.clone(),
)?;
```

そして function entry も `Vec<CpsRuntimeValue>` を受けるようにする。

```rust
fn eval_function_with_cps_values(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<CpsRuntimeValue>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
) -> CpsEvalResult<CpsRuntimeValue> {
    eval_continuations(
        module,
        function,
        function.entry,
        args,
        Vec::new(),
        active_handlers,
        guard_stack,
    )
}
```

root だけは VM 比較用に plain value へ戻す。

```rust
let result = eval_function_with_cps_values(...)?;
let vm = cps_value_to_vm(result)
    .ok_or(CpsEvalError::NonPlainRoot)?;
```

---

# 6. Milestone 8E: First-class resumption tests

`std::undet.once` に行く前に、小さいテストを入れる。
これが通らないなら、まだ第一級ではない。

## Test 1: resumption を tuple に入れる

```rust
#[test]
#[ignore = "Milestone 8: first-class resumption in tuple"]
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
"#).expect("first-class resumption tuple");
    });
}
```

期待値は VM と同じ。たぶん `1`。

## Test 2: resumption を list に入れる

```rust
#[test]
#[ignore = "Milestone 8: first-class resumption in list"]
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
"#).expect("first-class resumption list");
    });
}
```

この2つが Milestone 8 の gate。

---

# 7. Milestone 8F: CPS repr evaluator に同じ値ドメインを入れる

`cps_eval.rs` だけでは不十分。
`cps_repr.rs` にも同じ `CpsRuntimeValue` 相当があるはずなので、同じ変更を入れる。

見るべき点:

```text
- DirectCall args が plain 限定ではないか
- ApplyClosure args が plain 限定ではないか
- List primitive が VmValue 限定ではないか
- TupleGet / VariantPayload が VmValue 限定ではないか
- Resume が Resumption variant を読めるか
```

ここまでで、CPS eval と CPS repr eval が一致する必要がある。

---

# 8. Milestone 8G: Cranelift 側は ControlPtr lane

CPS eval / CPS repr eval が通ってから Cranelift に行く。

## 追加 lane

```rust
pub enum CpsReprAbiLane {
    ScalarI64,
    NativeFloat,
    RuntimeValuePtr,
    ThunkPtr,
    ResumptionPtr,
    ClosurePtr,
    ControlPtr,
    OpaqueI64,
    Unknown,
}
```

`ControlPtr` は、

```text
List<CpsOpaqueValue>
Tuple<CpsOpaqueValue>
Variant<CpsOpaqueValue>
```

の pointer。

## runtime object

`cps_runtime.rs` に registry を足す。

```rust
enum CpsControlObject {
    List(Vec<i64>),
    Tuple(Vec<i64>),
    Variant {
        tag: i64,
        has_value: bool,
        value: i64,
    },
}
```

`i64` は opaque handle。
中身が resumption か thunk か runtime value かは、その使用箇所で解釈する。

## helper API

```rust
#[no_mangle]
pub extern "C" fn yulang_cps_control_list_empty() -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_singleton(value: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_append(list: i64, value: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_merge(left: i64, right: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_is_empty(list: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_head(list: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_list_tail(list: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_tuple2(a: i64, b: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_tuple_get(tuple: i64, index: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_variant(tag: i64, has_value: i64, value: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_variant_tag_eq(value: i64, tag: i64) -> i64;

#[no_mangle]
pub extern "C" fn yulang_cps_control_variant_payload(value: i64) -> i64;
```

最初は `list<resumption>` 用なので、list / tuple2 / nil/just variant だけで十分。

---

# 9. Milestone 9: `std::undet.once` scalar-unwrapped

ここで初めて標準 once を試す。

```rust
#[test]
#[ignore = "Milestone 9: std undet once scalar-unwrapped"]
fn compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#).expect("std undet once scalar-unwrapped");
    });
}
```

root は int に潰す。
`opt` をそのまま print しない。

---

# 別LLに渡す新指示

```text
計画を修正する。

重要な理解:
- 第一級 resumption とは、CPS runtime 内で resumption が普通の値ドメインに属すること。
- 内部表現が VmValue と同一である必要はない。
- しかし list / tuple / variant / function arg / pattern には resumption が普通に流れなければならない。
- std::undet.once は queue に k を保存して、uncons で取り出し、k false を呼ぶ。専用 ContinuationArray だけでは不十分。

やること:
1. Milestone 7:
   std::undet.each + local once_dfs_int を追加して、fold/sub/closure callback を確認する。
   ApplyClosure が active_handlers / guard_stack を落としていないか見る。

2. Milestone 8:
   CpsRuntimeValue を拡張する:
     Plain(VmValue)
     Resumption
     Thunk
     Closure
     List(Vec<CpsRuntimeValue>)
     Tuple(Vec<CpsRuntimeValue>)
     Variant { tag, value }

3. List primitives を CpsRuntimeValue 対応にする:
   ListEmpty / ListSingleton / ListAppend / ListMerge / ListUncons / ListLen / ListIndex。
   ListUncons は nil または just(tuple(head, tail)) を CpsRuntimeValue::Variant で返す。

4. TupleGet / VariantTagEq / VariantPayload を CpsRuntimeValue 対応にする。

5. DirectCall / ApplyClosure の args を read_plain_value ではなく read_value に寄せる。
   function entry も Vec<CpsRuntimeValue> を受け取る。

6. first-class resumption tests を追加する:
   - k を tuple に入れて取り出して resume
   - k を list に入れて uncons して resume

7. CPS eval → CPS repr eval → Cranelift の順に進める。
   Cranelift では ControlPtr lane と control list/tuple/variant helpers を追加する。

禁止:
- std::undet.once 専用の ContinuationArray を作らない。
- VmValue::List に Resumption を混ぜない。
- ResumptionPtr と RuntimeValuePtr を同一視しない。
- list(k) / append queue [k] だけ special-case しない。
```

---

# まとめ

はい、**実装計画は変わる**。
今後は「継続用の配列とタプル」ではなく、

```text
CPS runtime の統一値ドメイン
+
ControlPtr / CpsRuntimeValue containers
+
first-class resumption tests
```

を中心に据えたほうがいい。

`std::undet.once` は、`k` を queue に入れて取り出す時点で、もう **第一級 resumption** を要求している。
だから、そこをごまかさずに値ドメインへ入れる方針に変えるのが、長期的にはいちばん安全だと思うよ〜。
