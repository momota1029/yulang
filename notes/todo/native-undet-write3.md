うん。
その違和感、**かなり正しい** よ〜。

結論から言うと、

> **「継続用の配列とタプルを新しく用意する」だけで `std::undet` を通そうとしているなら、たぶん危ない。**
> **ただし、それが “第一級の継続値を格納するための内部コンテナ” なら大丈夫。**

ここを区別しないと、あとで `.once` / `.list` / `.logic` が全部つらくなるねぇ。

---

# まず現在地

最新の `native-undet-plan.md` では、Phase 4 の recursive case、つまり `each_list(xs): [choice] int` のような recursive helper は通った扱いになっている。`InstallHandler` / `UninstallHandler`、runtime handler stack、`DirectCall` / `ApplyClosure` / `ForceThunk` への `active_handlers` threading で、caller の handler frame が recursive helper に見えるようになった、という状態だねぇ。

次の open は、

* `std::undet.each` がまだ `fold` / `sub::return` を使う
* `std::undet.once` には resumption queue が必要
* CPS executable が non-scalar Yulang values をまだ print できない

というところ。

そして標準 `std::undet.once` は実際に、`branch(), k -> loop(k true, append queue [k])` で resumption `k` を queue に保存し、`reject` 時に queue から取り出して `k false` する実装になっている。

つまり、ここから先は **resumption を値として保存・取り出し・再開できる必要がある**。
これを避けると、`std::undet.once` は根本的に無理だよ〜。

---

# 「第一級継続」とは何を意味するか

ここ、言葉が混ざりやすいねぇ。

## 必須: 第一級 resumption

Yulang の handler arm に出てくる `k` は、少なくとも backend では第一級値でないといけない。

つまり `k` は、

```text
- local variable に束縛できる
- tuple / variant / list / queue に入れられる
- 関数へ渡せる
- あとで取り出して resume できる
- multi-shot なら複数回呼べる
```

必要がある。

これは `std::undet.once` の queue がまさに要求している。

## 不要: source-level で「継続型」を一般公開すること

一方で、Yulang surface に `continuation` 型を公開するとか、`VmValue` に raw continuation を混ぜるとかは、今すぐ必要ではない。

必要なのは、native CPS backend 内で、

```rust
CpsRuntimeValue::Resumption(...)
```

または Cranelift 側で、

```text
ResumptionPtr
```

として、**値として流せること**。

---

# 「継続用の配列とタプル」はいつ OK か

## OK なケース

これは OK。

```text
ControlList<ControlValue>
ControlTuple<ControlValue>
ControlVariant<ControlValue>
```

のような、**CPS runtime 専用の control-value container** を用意する。

その中身として、

```text
ResumptionPtr
ThunkPtr
ClosurePtr
RuntimeValuePtr
ScalarI64
```

を入れられる。

この場合、配列やタプルは「第一級継続を入れる箱」なので問題ない。

## 危ないケース

これは危ない。

```text
ContinuationArray {
    code_ids: Vec<i64>,
    env0: Vec<i64>,
    env1: Vec<i64>,
    ...
}
```

みたいに、`std::undet.once` の queue 専用に continuation の中身をばらして保存する。

これだと、

* handler stack snapshot
* guard stack snapshot
* rebase された handler frame
* captured env
* multi-shot clone
* closure callback
* nested handler

をすぐ失う。
しかも `k` が一般の値として流れないので、`.list` / `.logic` / user-defined nondet collector に進めなくなる。

---

# りなの判断

**継続は第一級にした方がいい。**
というより、`std::undet` をちゃんと動かすなら避けられない。

ただし実装はこうでいい。

```text
第一級 continuation = opaque handle
```

つまり、source-visible な tagged value ではなく、CPS runtime の opaque object として持つ。

---

# 推奨する内部表現

## CPS evaluator 側

`CpsRuntimeValue` をこういう方向にする。

```rust
#[derive(Debug, Clone, PartialEq)]
enum CpsRuntimeValue {
    Plain(runtime::VmValue),

    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),

    ControlList(Rc<Vec<CpsRuntimeValue>>),
    ControlTuple(Vec<CpsRuntimeValue>),
    ControlVariant {
        tag: core_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },
}
```

ここで重要なのは、`ControlList` の中身が `VmValue` ではなく `CpsRuntimeValue` であること。

そうすると、

```text
list<resumption>
list<thunk>
tuple(resumption, queue)
opt just (k, queue)
```

を表せる。

`std::undet.once` のこの部分に必要だねぇ。

```yulang
std::opt::opt::just (k, queue) -> loop(k false, queue)
```

`k` は `Resumption`、`queue` は `ControlList` として取り出せる必要がある。

---

# Cranelift / object 側

Cranelift では全部 `i64` opaque handle でよい。

```text
ScalarI64
RuntimeValuePtr
ThunkPtr
ResumptionPtr
ClosurePtr
ControlPtr
OpaqueI64
```

を分ける。

追加するならこう。

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

`ControlPtr` は `ControlList` / `ControlTuple` / `ControlVariant` 用。
ただし最初は `ControlList` だけでもいい。

---

# 次に実際に書くべきコード

ここからが大事。

## Milestone 7: `std::undet.each` + local once

今の `native-undet-plan.md` でも次は `std::undet::each` を local DFS once helper と一緒に戻す、とされている。

これはまだ queue-backed `std::undet.once` ではない。
まずは `std::undet.each` が `fold` / `sub::return` / closure callback を通れるかを見る。

### 追加するテスト

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

パス名は実際の export に合わせて調整してねぇ。
`branch` / `reject` が prelude 経由で見えるなら短くしてもいい。

### ここで失敗したら見る場所

`std::undet.each` は `fold` と `sub::return` を使う。
だから失敗原因はだいたいこのどれか。

```text
1. fold callback closure に active handler stack が渡らない
2. sub::return の handler が dynamic handler stack で見つからない
3. callback が thunk として返り、force site の handler が使われない
4. DirectCall は直ったが ApplyClosure が context を落としている
```

### 実際に書くべき修正

`CpsStmt::ApplyClosure` の evaluator と Cranelift lowering を確認する。

CPS eval 側はこうあるべき。

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

Cranelift 側も同じで、closure entry call に current handler stack / guard stack を hidden context として渡す。
`DirectCall` だけ通して `ApplyClosure` で落とすと、`fold` が必ず詰まる。

---

# Milestone 8: queue-backed once

ここがユーザーの違和感の本丸だねぇ。

`std::undet.once` は resumption queue を使う。
なので、ここで **第一級 resumption container** が必要になる。

## やるべきこと

### 1. `CpsRuntimeValue` に control container を足す

```rust
enum CpsRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),

    ControlList(Rc<Vec<CpsRuntimeValue>>),
    ControlTuple(Vec<CpsRuntimeValue>),
    ControlVariant {
        tag: core_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },
}
```

### 2. primitive eval を `CpsRuntimeValue` 対応にする

今は unhandled primitives を `runtime::vm::primitive::apply_primitive` に委譲している。これは `each_head` には有効だった。
でも resumption queue では足りない。`apply_primitive` は `VmValue` しか扱えないからねぇ。

なので、CPS 側に専用 primitive evaluator を作る。

```rust
fn eval_cps_primitive_value(
    op: core_ir::PrimitiveOp,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    match op {
        core_ir::PrimitiveOp::ListEmpty => {
            Ok(CpsRuntimeValue::ControlList(Rc::new(Vec::new())))
        }

        core_ir::PrimitiveOp::ListSingleton => {
            let [value] = one_arg(args)?;
            Ok(CpsRuntimeValue::ControlList(Rc::new(vec![value])))
        }

        core_ir::PrimitiveOp::ListAppend => {
            let (list, value) = two_args(args)?;
            append_control_list(list, value)
        }

        core_ir::PrimitiveOp::ListMerge => {
            let (left, right) = two_args(args)?;
            merge_control_lists(left, right)
        }

        core_ir::PrimitiveOp::ListUncons => {
            let [list] = one_arg(args)?;
            uncons_control_list_as_opt(list)
        }

        _ => {
            let plain_args = args
                .into_iter()
                .map(into_plain_for_primitive)
                .collect::<CpsEvalResult<Vec<_>>>()?;

            runtime::vm::primitive::apply_primitive(op, &plain_args)
                .map(CpsRuntimeValue::Plain)
                .map_err(|_| CpsEvalError::UnsupportedPrimitive { op })
        }
    }
}
```

### 3. `uncons` は control variant を返す

`std::list::uncons queue` は `opt (k, queue)` を返す。
`k` が `Resumption` の場合、`VmValue::Tuple` では表せない。

だからこう返す。

```rust
fn uncons_control_list_as_opt(
    list: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::ControlList(items) = list else {
        return Err(...);
    };

    if items.is_empty() {
        return Ok(CpsRuntimeValue::ControlVariant {
            tag: core_ir::Name("nil".to_string()),
            value: None,
        });
    }

    let head = items[0].clone();
    let tail = CpsRuntimeValue::ControlList(Rc::new(items[1..].to_vec()));

    Ok(CpsRuntimeValue::ControlVariant {
        tag: core_ir::Name("just".to_string()),
        value: Some(Box::new(CpsRuntimeValue::ControlTuple(vec![
            head,
            tail,
        ]))),
    })
}
```

パス付き tag が必要なら `std::opt::opt::nil` / `std::opt::opt::just` の canonical name に合わせる。

---

# pattern binding も `CpsRuntimeValue` 対応にする

ここを忘れると必ず詰まる。

`std::undet.once` は、

```yulang
std::opt::opt::just (k, queue) -> loop(k false, queue)
```

という pattern を使う。

つまり、pattern binder が `VmValue` だけでなく、

```text
ControlVariant just
ControlTuple(k, queue)
```

を destruct できないといけない。

## 書くべき関数

```rust
fn bind_pattern_cps_value(
    pattern: &runtime::Pattern,
    value: CpsRuntimeValue,
    locals: &mut HashMap<core_ir::Path, CpsValueId>,
    values: &mut Vec<Option<CpsRuntimeValue>>,
) -> CpsEvalResult<()> {
    match pattern {
        runtime::Pattern::Bind { name, .. } => {
            let id = fresh_or_existing_value_for_bind(name);
            write_value(values, id, value);
            locals.insert(core_ir::Path::from_name(name.clone()), id);
            Ok(())
        }

        runtime::Pattern::Tuple { items, .. } => {
            let CpsRuntimeValue::ControlTuple(values_tuple) = value else {
                return Err(...);
            };

            if items.len() != values_tuple.len() {
                return Err(...);
            }

            for (pat, item) in items.iter().zip(values_tuple) {
                bind_pattern_cps_value(pat, item, locals, values)?;
            }

            Ok(())
        }

        runtime::Pattern::Variant { tag, value: payload_pat, .. } => {
            let CpsRuntimeValue::ControlVariant {
                tag: actual,
                value: payload,
            } = value else {
                return Err(...);
            };

            if actual != *tag {
                return Err(...);
            }

            match (payload_pat.as_deref(), payload) {
                (Some(pat), Some(payload)) => {
                    bind_pattern_cps_value(pat, *payload, locals, values)
                }
                (None, None) => Ok(()),
                _ => Err(...),
            }
        }

        runtime::Pattern::Wildcard { .. } => Ok(()),

        _ => {
            // Existing plain VmValue path can stay separate.
            Err(...)
        }
    }
}
```

ただし compiler lowering 側の pattern binding はすでに CPS IR の stmt として落ちている可能性があるので、実際には evaluator で pattern を直接扱う場所がどこかを確認する必要がある。
もし lowering 時に `VariantPayload` / `TupleGet` に分解しているなら、そちらを `CpsRuntimeValue` 対応にする。

---

# Cranelift 側の ControlPtr

CPS eval / CPS repr eval が通ったら、Cranelift に進む。

ここで「継続用の配列とタプル」が出てくるなら、**ControlPtr として実装する** のが良い。

## runtime object

```rust
enum CpsControlObject {
    List(Vec<i64>),
    Tuple(Vec<i64>),
    Variant {
        tag: u64,
        value: i64, // 0 means none, or use separate flag
    },
}
```

`i64` は opaque handle。
中身は resumption pointer, thunk pointer, runtime value pointer, scalar boxed value などを区別しない。
必要なら tag table / lane table を持つ。

## helper API

```rust
#[no_mangle]
extern "C" fn yulang_cps_control_list_empty() -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_singleton(value: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_append(list: i64, value: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_merge(left: i64, right: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_is_empty(list: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_head(list: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_list_tail(list: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_tuple2(a: i64, b: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_tuple_get(tuple: i64, index: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_variant(tag: i64, has_value: i64, value: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_variant_tag_eq(variant: i64, tag: i64) -> i64;

#[no_mangle]
extern "C" fn yulang_cps_control_variant_payload(variant: i64) -> i64;
```

これなら、`std::undet.once` の queue を表せる。

---

# でも最初はもっと小さくていい

`std::undet.once` 用に必要な最小はこれだけ。

```text
ControlList<opaque i64>
ControlTuple2<opaque i64, opaque i64>
ControlVariant nil/just
```

つまり、

```text
[]                       // nil queue
[k]                      // singleton queue
append queue [k]          // queue push
uncons queue              // nil or just(k, queue)
```

だけでよい。

`.list` / `.logic` は後回しでいい。

---

# 「継続を第一級にする」ためのテスト

これを Milestone 8 の前に入れると安心。

## テスト1: resumption を tuple に入れて取り出す

```yulang
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        my pair = (k, 0)
        case pair:
            (r, _) -> r true
    v -> if v: 1 else: 2
```

期待: `1`

## テスト2: resumption を list に入れて取り出す

```yulang
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        case std::list::uncons [k]:
            std::opt::opt::nil -> 0
            std::opt::opt::just (r, _) ->
                if r true: 1 else: 2
    v -> if v: 10 else: 20
```

期待: `1`

これはまさに第一級 resumption の確認だねぇ。
これが通らないなら、`std::undet.once` に行ってはいけない。

---

# 次のLLに渡すべき修正版指示

```text
現在の懸念:
「継続用の配列とタプルを作る」だけでは危険。
std::undet.once は resumption k を queue に保存し、あとで k false する。
したがって resumption は第一級の CPS runtime value / opaque handle として扱う必要がある。

方針:
- Continuation/resumption を source-level VmValue に混ぜない。
- ただし CPS runtime では CpsRuntimeValue::Resumption / ResumptionPtr として第一級にする。
- 配列・タプルを作るなら、それは ControlList / ControlTuple / ControlVariant として、CpsRuntimeValue や opaque i64 handle を入れる container にする。
- std::undet.once 専用の ContinuationArray にしない。
- VmValue::List に Resumption を雑に入れない。

次の作業:
1. Milestone 7:
   std::undet.each + local once_dfs_int を追加。
   失敗したら ApplyClosure が active_handlers / guard_stack を落としていないか見る。
2. Milestone 8 の前に:
   resumption を tuple/list に入れて取り出して resume する小さい test を追加する。
3. CPS eval:
   CpsRuntimeValue に ControlList / ControlTuple / ControlVariant を足す。
   ListEmpty/ListSingleton/ListAppend/ListUncons を CpsRuntimeValue 対応にする。
4. CPS repr eval:
   同じ control container semantics を実装する。
5. Cranelift:
   ControlPtr lane を足し、control list/tuple/variant helper を cps_runtime に実装する。
6. std::undet.once:
   まず scalar-unwrapped case だけを通す。
   opt をそのまま print しようとしない。

絶対禁止:
- std::undet.once だけを special-case する。
- ContinuationArray に code/env をばらして保存する。
- ResumptionPtr を RuntimeValuePtr と同じ扱いにする。
- value backend に resumption を入れる。
```

---

# りなの答え

**そのままだと大丈夫じゃない。**
「継続用配列とタプル」が、第一級 resumption を入れるための control container なら大丈夫。
でも「continuation を第一級にせず、`std::undet.once` 用にだけ配列で持つ」なら、たぶん後で壊れる。

`std::undet` をちゃんと動かしたいなら、次の軸はこれだねぇ。

```text
ResumptionPtr を第一級 CPS value にする
ControlList / ControlTuple / ControlVariant を用意する
Pattern / primitive / Cranelift helper を ControlPtr 対応にする
```

この方針なら、`once` だけでなく、将来 `.list` / `.logic` / user-defined nondet collector にも進めると思うよ〜。
