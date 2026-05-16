見た感じ、これは **print だけ直す** とか **if だけ直す** じゃなくて、native CPS 周りの “継続と値 lane と handler env” が複数箇所で崩れてる。特に round-7 では、`Display::show` / `Debug::debug` の組み立て、`for` body 内 `if` の var write、range + console effect、`loop with` の if join が別々の症状として並んでるねぇ。`notes/bugs/index.md` でもこの 4 件はそれぞれ native の値破損として記録されてる。

以下、そのまま別 LLM に渡せるレベルの指示文として書くよ〜。

---

# yulang native CPS 回帰修正 指示書

## 0. ゴール

対象 repo は `momota1029/yulang`。

`notes/bugs/index.md` の round-7 native 回帰のうち、まず次の 4 系統を直す。

1. `native_list_show_returns_close_bracket.yu`
   `[1, 2, 3].show` / `.debug` が native で `"]"` だけになる。

2. `native_for_if_var_write_lost.yu`
   `for` body 内の `if` branch で `&var = ...` すると native で var write が全部消える。

3. `native_for_range_console_only_first.yu`
   `for x in 0..<3: say x.show` が native で 1 回目しか実行されない。

4. `native_loop_with_returns_bool_lane.yu`
   `loop initial with: our loop state = if cond: state else: loop (...)` の戻り値が native で `state` ではなく cond の bool lane、つまり `0` / `1` になる。

`index.md` 上の記述では、`list.show` は root pretty-print ではなく `Display::show` / `Debug::debug` の組み立て側、`for-if-var` は `if` branch 経由の write-back path、`range-console` は range Fold の continuation、`loop-with` は if branch join 直後の値 lane が怪しい、と分かれている。

---

## 1. 最初に regression test を足す

既存の native CPS テストは `crates/yulang-compile/src/lib.rs` にある。すでに `assert_source_cps_repr_display_with_std` があり、これは **CPS eval → CPS repr eval → CPS repr JIT** の 3 段を同じ期待値で比べるので、今回の切り分けにちょうどいい。helper 内では `YULANG_TEST_DUMP_CPS` が立っていると CPS IR も dump される。

既存テストには `runs_var_update_in_for_loop_through_cps_repr` がすでにあり、これは `for` + var write の if 抜きケースを通している。だから今回追加するのは **if 入りの var write** だよ〜。

`crates/yulang-compile/src/lib.rs` の `mod tests` 内、既存の `runs_var_update_in_for_loop_through_cps_repr` の近くに以下を追加する。

```rust
#[test]
fn runs_list_show_and_debug_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
[1, 2, 3].show
["a", "b"].show
[1, 2, 3].debug
["a", "b"].debug
"#,
        vec!["[1, 2, 3]", "[a, b]", "[1, 2, 3]", "[a, b]"],
    )
    .expect("CPS repr native display");
}

#[test]
fn runs_string_concat_smoke_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
"[" + "1" + "]"
"#,
        vec!["[1]"],
    )
    .expect("CPS repr native display");
}

#[test]
fn runs_var_update_in_for_if_body_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
my $c = 0
for x in 0..<10:
    if x < 5:
        &c = $c + x
    else:
        ()
$c
"#,
        vec!["10"],
    )
    .expect("CPS repr native display");
}

#[test]
fn runs_var_update_in_for_if_else_body_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
my $c = 0
for x in 0..<10:
    if x < 5:
        ()
    else:
        &c = $c + x
$c
"#,
        vec!["35"],
    )
    .expect("CPS repr native display");
}

#[test]
fn runs_loop_with_if_result_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
use std::flow::loop

my f(start: int): int = loop start with:
    our loop state =
        if state == 5:
            state
        else:
            loop (state + 1)

f 5
f 4
f 3
"#,
        vec!["5", "5", "5"],
    )
    .expect("CPS repr native display");
}

#[test]
fn runs_plain_if_result_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
my f(x: int): int =
    if x == 0:
        7
    else:
        9

f 0
f 1
"#,
        vec!["7", "9"],
    )
    .expect("CPS repr native display");
}
```

`range + console` は stdout capture が必要なら別 harness が要る。まずは console effect を自前 handler に置き換えた形で “3 回 handler が呼ばれる” テストを足すといい。

```rust
#[test]
fn runs_range_for_with_effect_body_through_cps_repr() {
    assert_source_cps_repr_display_with_std(
        r#"
act log:
    pub put: int -> ()

my collect(body: [log] (), acc: list int): list int = catch body:
    log::put n, k -> collect(k (), [..acc, n])
    v -> acc

collect ({
    for x in 0..<3:
        log::put x
}) []
"#,
        vec!["[0, 1, 2]"],
    )
    .expect("CPS repr native display");
}
```

そのあと stdout そのものも見るなら、CLI integration で `yulang run --native` の stdout を見るテストを別途足す。

---

## 2. 修正順序

おすすめ順はこれ。

1. **`loop with` の bool lane 問題を先に切る**
2. **`for` body 内 `if` + var write を直す**
3. **`list.show` / `.debug` を再確認する**
4. **range + console continuation を直す**

理由は、`list.show` は prelude 側で `"[ " + show_list_items xs + "]"` 型の組み立てをしていて、内部に `case` / `if` / recursive helper / `StringConcat` がある。`if` join や CPS repr lane が壊れていると `list.show` も `"]"` だけ残る可能性が高い。stdlib 側の `Display list` / `Debug list` 実装は素直な実装なので、ここを native 専用 workaround にしないでねぇ。

---

## 3. `loop with` が bool lane になる問題

### 症状

`native_loop_with_returns_bool_lane.yu` は、`if state == 5: state else: loop (state + 1)` の結果が `state` ではなく `state == 5` の bool に潰れる。期待は全部 `5`、native は `1` / `0` / `0`。

### まず見る場所

* `crates/yulang-native/src/cps_lower.rs`

  * `lower_if`
  * `lower_handler_body_if`
  * `lower_handled_if`
  * `lower_handled_effect_condition_if`

通常の `lower_if` は、cond を branch にだけ使い、then/else の値を `merge_cont` の引数として渡している。つまり CPS IR の時点では、`cond` value と `result` value は別 ID になるはず。

handler body 用の `lower_handler_body_if` も merge continuation を作って branch arm の値を合流させている。

一方、`lower_handled_if` / `lower_handled_effect_condition_if` は branch arm 内で `lower_handled_body(..., value_cont)` を直接呼び、明示的な merge continuation を作らない。この経路は effect handler scope 内の if に使われるので、`loop with` の handler/reentry と絡むならここが濃い。

### 切り分け

追加した `runs_plain_if_result_through_cps_repr` を先に走らせる。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_plain_if_result_through_cps_repr -- --nocapture
```

* これが落ちるなら、plain branch の CPS repr / JIT branch lowering が壊れている。
* これが通って `runs_loop_with_if_result_through_cps_repr` だけ落ちるなら、handler/reentry/`loop with` 専用経路が壊れている。

次に CPS dump を見る。

```bash
YULANG_TEST_DUMP_CPS=1 RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_loop_with_if_result_through_cps_repr -- --nocapture
```

見る点:

* `state == 5` の結果 value id が、merge continuation の result param と同じ扱いになっていないか。
* then branch が `state` を `Continue { target: merge_cont, args: [state] }` しているか。
* else branch が `loop (state + 1)` の戻り値を `Continue { target: merge_cont, args: [...] }` しているか。
* merge continuation の param が最終 return / handler value arm に流れているか。

### 修正指針

#### CPS IR がすでに間違っている場合

`cps_lower.rs` 側を直す。

特に `lower_handled_if` / `lower_handled_effect_condition_if` が “式としての if” を値合流させず、branch condition や branch 内 effect の戻り値をそのまま外へ漏らしていないか見る。

修正方針:

* 式 value が必要な if は、必ず `merge_cont` と `result` value を作る。
* then/else body の値を `merge_cont` に渡す。
* `value_cont` が `Some` の場合でも、branch 内から直接 `value_cont` へ行くかどうかを慎重に分ける。

  * tail position の if なら branch から `value_cont` へ直接でよい。
  * non-tail / handler reentry value を持つ if ならローカル merge を作る。

#### CPS IR は正しいが CPS repr eval / JIT だけ間違う場合

`crates/yulang-native/src/cps_repr.rs` 側を見る。

`cps_repr.rs` の ABI lane analysis では branch terminator の return lane を then/else continuation の return lane merge として扱っている。cond の lane を return lane に入れる設計ではない。ここで cond が混ざっているなら bug。

repr eval の branch 実行も cond は `current` の分岐先選択にだけ使っている。

なので JIT だけ落ちるなら、`cps_repr_cranelift` 側の branch lowering / continuation return lane materialization を見る。具体的には:

* branch cond の i64 value を function return slot に入れていないか。
* `then_cont` / `else_cont` の continuation return lane を caller continuation の return lane として使っているか。
* merge continuation param の value lane が `ScalarI64` / `RuntimeValuePtr` のどちらかに正しく伝播しているか。

---

## 4. `for` body 内 `if` の var write が消える問題

### 症状

`native_for_if_var_write_lost.yu` は、`for x in 0..<10:` の中で `if x < 5: &c = $c + x` と書くと、VM は `10`、native は `0` になる。if 抜きの `for x: &c = $c + x` は通るので、`for` や var handler 単体ではなく **if branch 経由の write-back path** が詰まっている。

### まず見る場所

`crates/yulang-native/src/cps_lower.rs` の `lower_handled_block`。

理由:

* var write は effect handler / `ResumeWithHandler` env overlay を通る。
* `for` body は handler scope / callback scope 内に入る。
* `lower_handled_body` は `ExprKind::If` を見たら `lower_handled_if` に送るが、`lower_handled_block` の `Stmt::Expr(expr)` は多くのケースで直接 `lower_expr(expr)` に落ちる。
* `if` の branch 内に effect があるのに、non-tail statement として `lower_expr` 側へ落ちると、handler-aware lowering が通らず var handler env update が外へ伝播しない可能性が高い。

### 直す方針

`lower_handled_block` の `runtime::Stmt::Expr(expr)` 分岐で、generic `lower_expr(expr)?` に落ちる前に、次の条件を入れる。

```rust
let expr_may_perform =
    !collect_expr_performed_effects(expr).is_empty()
    || self.expr_may_perform_when_evaluated(expr);

if expr_may_perform {
    let is_tail_stmt = stmts[index + 1..].is_empty() && tail.is_none();
    let branch_value_cont = if is_tail_stmt { value_cont } else { None };

    let effect = self.lower_handled_body(
        expr,
        expected_effects,
        handler,
        branch_value_cont,
    )?;

    if is_tail_stmt {
        return Ok(effect);
    }

    let rest_effect = self.lower_handled_block(
        &stmts[index + 1..],
        tail,
        expected_effects,
        handler,
        value_cont,
    )?;

    if !handled_effects_compatible(expected_effects, &rest_effect, &effect) {
        return Err(CpsLowerError::UnsupportedExpr {
            kind: "handler effect mismatch",
        });
    }

    return Ok(effect);
}
```

実装時の注意:

* `BindHere` の special-case と `effect_apply_nested(expr)` の direct perform handling より前後関係を慎重に見る。
* `BindHere` は今の特殊処理を壊さない。
* `effect_apply_nested(expr)` は top-level perform をうまく扱っているので、`If` や `Block` のような nested effect expression を拾う branch を足す形が安全。
* tail statement の場合だけ `value_cont` を渡す。
* non-tail statement では `value_cont=None` にして、if の then/else が handler scope を抜けずに rest-of-block へ続くようにする。
* rest lowering のあと `handled_effects_compatible` / `join_handled_effect` 相当で effect 整合性を見る。

この修正の狙いは、`if` branch 内の `&c = ...` を handler-aware path、つまり `ResumeWithHandler` env overlay が効く path で lower すること。CPS eval / repr には handler env overlay の仕組みがあり、`ResumeWithHandler` は env update を captured stack / active handler stack に反映するように書かれている。

### この修正後に走らせるテスト

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_body_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_else_body_through_cps_repr -- --nocapture
```

既存の if 抜きテストも必ず走らせる。if 入りだけ直して if 抜きが壊れるなら、handler env overlay か rest continuation の扱いが過剰に変わっている。

---

## 5. `list.show` / `debug` が `"]"` だけになる問題

### 症状

`native_list_show_returns_close_bracket.yu` は、`[1, 2, 3].show` / `["a", "b"].show` / `.debug` が native で `"]"` だけになる。root pretty-print の list 表示は native でも OK なので、list runtime value の表示全体ではなく `Display::show` / `Debug::debug` の文字列組み立て側が壊れている。

prelude の実装はこういう形。

```yulang
our xs.show = "[" + show_list_items xs + "]"
our xs.debug = "[" + debug_list_items xs + "]"
```

`show_list_items` / `debug_list_items` は `uncons` + `if std::list::is_empty tail` + recursive call で要素文字列を作る。

`StringConcat` primitive 自体は普通に left/right を `StringTree::concat(left, right)` しているので、最初から primitive を疑うより、CPS lowering / CPS repr / branch join / direct call force の切り分けを先にやる。

### 切り分けテスト

追加した smoke test を先に見る。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_string_concat_smoke_through_cps_repr -- --nocapture
```

* これが落ちるなら `StringConcat` / string value lane の問題。
* これが通るなら `list.show` 固有、つまり helper recursion / `case` / `if` / direct call result force の問題。

次に actual test。

```bash
YULANG_TEST_DUMP_CPS=1 RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_list_show_and_debug_through_cps_repr -- --nocapture
```

見る点:

* `show_list_items__mono...` の CPS function が生成されているか。
* `"[", show_list_items xs, "]"` の concat chain が IR 上で残っているか。
* `show_list_items` の `case std::list::uncons xs` が then/else arm value を merge しているか。
* `if std::list::is_empty tail` の cond value が result value と混ざっていないか。
* `DirectCall show_list_items` の戻り値が `ForceThunk` されるべきなのにされていない、または逆に thunk を値として concat に渡していないか。

### 修正方針

まず 3. と 4. の `if` / handler-aware lowering 修正後に再実行する。`list.show` は `case` と `if` を内包しているので、`loop with` の bool lane 修正で一緒に直る可能性がある。

それでも `"]"` のままなら、次を見る。

#### CPS eval では OK、CPS repr eval / JIT で NG

`cps_repr.rs` の value kind / ABI lane analysis を見る。`StringConcat` の result lane は `RuntimeValuePtr` になっている。

見る点:

* `StringConcat` result が `RuntimeValuePtr` なのに `ScalarI64` / `OpaqueI64` に潰れていないか。
* `DirectCall show_list_items` の return lane が `RuntimeValuePtr` になっているか。
* branch continuation return lane merge が `RuntimeValuePtr` を保っているか。
* `format_native_i64_value` は String を flat string にするだけなので、表示関数側の問題ではない。既存 helper がそう処理している。

#### CPS IR からすでに `"]"` だけ

`cps_lower.rs` 側を見る。

候補:

* `unused_pure_let` が concat の左側を誤って捨てている。
* direct call inlining / thunk forcing が `show_list_items` の結果を捨てている。
* `lower_match` / `lower_if` の merge result が cond / unit / final literal に潰れている。
* string interpolation 経由でも `vals = ]` になるなら、`Display::show` を使う全経路で同じ helper result が落ちている。

ここで `prelude.yu` に native 専用 workaround を入れない。例えば `list.show` だけ host pretty-print に逃がすのは、`.debug`、string interpolation、role method dispatch、recursive helper の bug を隠すだけになる。

---

## 6. `for x in range: say x.show` が 1 回で止まる問題

### 症状

`native_for_range_console_only_first.yu` は、`for x in 0..<3: say x.show` が VM では `0`, `1`, `2`, `()` を出すのに、native は `0`, `()` で止まる。list iteration + say は OK、range + var write も OK。つまり “console effect” と “range fold continuation” の組み合わせが濃い。

### まず見る場所

* `lib/std/range.yu`

  * `fold`
  * `fold_from`
  * `fold_ints`
  * `for` desugaring 先の range helper
* `crates/yulang-native/src/cps_lower.rs`

  * `target_may_perform_when_called`
  * `expr_contains_indirect_apply`
  * `direct_apply_path`
  * `lower_handled_effectful_call_let`
  * `lower_handled_effectful_apply_let`
* `crates/yulang-native/src/cps_eval.rs`

  * `EffectfulCall`
  * `Perform`
  * `capture_return_frames_inside_prompt`
* `crates/yulang-native/src/cps_repr.rs`

  * `EffectfulCall`
  * `Perform`
  * `capture_return_frames_inside_prompt_repr`

CPS eval / repr eval は `InstallHandler` 時に `prompt_exit` 付き return frame を積み、`Perform` 時に `capture_return_frames_inside_prompt` で handler prompt の内側だけ resumption に保存する構造になっている。

また `EffectfulCall` は post-call continuation を return frame として push する。これがないと、effect 発火時に “range の次 iteration” が resumption に入らない。

### 直す方針

range fold の body が console effect を起こすとき、その fold helper 呼び出しは sync `DirectCall` ではなく、post continuation を return frame に積む `EffectfulCall` / `EffectfulApply` 経路に入る必要がある。

具体的に見ること:

1. `for x in 0..<3: say x.show` の CPS dump を取る。

   ```bash
   YULANG_TEST_DUMP_CPS=1 RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_range_for_with_effect_body_through_cps_repr -- --nocapture
   ```

2. range fold helper の呼び出しが `CpsTerminator::EffectfulCall` になっているか見る。

3. もし `DirectCall` のままなら、`target_may_perform_when_called` / `expr_contains_indirect_apply` が callback effect を見逃している。

4. 修正は “全部の direct call を effectful にする” ではなく、次の条件に絞る。

   * active handler scope 内にいる。
   * callee が higher-order helper で callback を apply する。
   * callee の body または引数 callback の static type が effectful。
   * return type が thunk / effect row を持つ。
   * 既存の `higher_order_helper` flag と `target_may_perform_when_called` を使えるならそこへ寄せる。

5. `EffectfulCall` に変わったら、`Perform` 時の captured resumption に range の “next iteration” continuation が入るか見る。

6. `capture_return_frames_inside_prompt` が prompt boundary より内側の ordinary continuation だけを保存しているか見る。ここを雑に handler frame filter で直さない。`notes/bugs/index.md` の round-6 メモでも、handler frame を消す・suffix を切るだけの修正は `.once` や var handler 更新を壊す、と記録されている。

### 走らせるテスト

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_range_for_with_effect_body_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_list_each_through_cps_repr -- --nocapture
```

range fold を直すと `std::undet` / open range / handler prompt 周りに触れがちだから、`undet` 系 regression も一緒に走らせる。

---

## 7. 触ってはいけない方向

これは避ける。

### `prelude.yu` の `list.show` を特殊化しない

`Display list` は stdlib 上では自然な `StringConcat` + recursive helper なので、ここだけ native 用に逃がすと根本原因が残る。

### `StringConcat` をいきなり疑わない

primitive 実装は left/right を concat しているだけ。pure concat smoke が落ちたときだけ触る。

### すべての `DirectCall` を `EffectfulCall` にしない

一見 range + console は直るかもしれないけど、return frame が過剰に増えて handler scope / `sub:return` / `undet.once` が壊れる。higher-order helper / callback effect / active handler scope に絞る。

### handler stack を雑に filter しない

`InstallHandler` は `value` continuation と `escape` continuation を分け、eval 側では `prompt_exit` metadata 付き return frameを積む設計になっている。ここを “内側 handler を消す” みたいに直すと、`.once` の value arm 二重適用や var handler write-back の再発を呼ぶ。

---

## 8. 具体的な作業チェックリスト

### Step A: tests 追加

`crates/yulang-compile/src/lib.rs` に上の regression tests を追加する。

まず単発で落ちることを見る。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_list_show_and_debug_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_body_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_loop_with_if_result_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_range_for_with_effect_body_through_cps_repr -- --nocapture
```

### Step B: bool lane を直す

1. `runs_plain_if_result_through_cps_repr` と `runs_loop_with_if_result_through_cps_repr` を比較。
2. plain if も落ちるなら CPS repr/JIT branch lowering。
3. loop-with だけ落ちるなら `lower_handled_if` / handler reentry 経路。
4. CPS dump で cond value と merge result value が混ざっていないか見る。
5. 必要なら `lower_handled_if` に tail/non-tail の値 merge を入れる。

### Step C: for-if-var を直す

1. `lower_handled_block` の non-tail `Stmt::Expr(expr)` で nested effect expression を `lower_expr` に落とさない。
2. `collect_expr_performed_effects(expr)` または `expr_may_perform_when_evaluated(expr)` が true なら `lower_handled_body` に送る。
3. non-tail では `value_cont=None`、tail では元の `value_cont`。
4. rest-of-block を continuation として残す。
5. `handled_effects_compatible` を保つ。

### Step D: list.show を再確認

1. bool lane / for-if-var 修正後に `runs_list_show_and_debug_through_cps_repr` を再実行。
2. pure concat smoke が通っているなら `StringConcat` ではなく helper recursion / branch / direct call force を見る。
3. `show_list_items` の CPS IR を dump して、concat chain と branch merge を見る。
4. CPS eval OK / repr NG なら `cps_repr.rs` lane analysis。
5. CPS IR NG なら `cps_lower.rs` の `lower_match` / `lower_if` / direct call force / unused pure let。

### Step E: range + console を直す

1. `runs_range_for_with_effect_body_through_cps_repr` の CPS dump を見る。
2. range fold helper が `DirectCall` なら effectful 判定漏れ。
3. callback effect を持つ range fold helper を `EffectfulCall` / `EffectfulApply` に落とす。
4. `Perform` 時に next iteration continuation が captured return frame に入るか見る。
5. `undet` 系を必ず再実行。

---

## 9. 最後に走らせるコマンド

最小セット:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_string_concat_smoke_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_list_show_and_debug_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_body_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_else_body_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_plain_if_result_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_loop_with_if_result_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_range_for_with_effect_body_through_cps_repr -- --nocapture
```

既存 regression セット:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_list_each_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_for_loop_return_escape_through_cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_for_loop_sub_return_value_in_later_expression_through_cps_repr -- --nocapture
```

広め:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_
RUSTC_WRAPPER= cargo test -q
```

---

## 10. まとめの修正候補

一番濃い実装修正はこの 2 つだねぇ。

### 第一候補: `lower_handled_block` の nested effect expression routing

`for` body 内 `if` の var write 消失は、`Stmt::Expr(if ...)` が handler-aware lowering を通らず `lower_expr` に落ちているのが本命。
`lower_handled_block` で nested effect を含む expression を `lower_handled_body` に送って、non-tail なら `value_cont=None`、tail なら元の `value_cont` を渡す。

### 第二候補: CPS repr / JIT の branch return lane

`loop with` が cond の `0` / `1` を返すなら、branch cond lane が continuation return lane に混ざっている。
CPS IR が正しければ `cps_repr` / JIT 側、CPS IR から間違っていれば `lower_handled_if` 側。

この 2 つを直したあと `list.show` が直る可能性は高い。残った `range + console` は、range fold helper が callback effect を見逃して sync `DirectCall` になっていないかを見て、必要なら active handler scope 内の higher-order helper call を `EffectfulCall` / `EffectfulApply` に寄せる。
