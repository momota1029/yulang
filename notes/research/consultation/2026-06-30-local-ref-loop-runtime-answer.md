# ChatGPT Pro consultation answer: local mutable ref and loop runtime plan

## 結論

VM レベルの `LocalRefCell` は、この性能問題に対して正しい方向である。ただし、単純な `Rc<RefCell<Value>>` のような「共有 heap cell」をそのまま入れるのは危険である。Yulang の現在の local var lowering は、local state を algebraic effect handler で表現しているので、captured continuation / multi-shot resume の下では state が continuation とどう一緒に複製されるかを明示する必要がある。

推奨方針は次の形である。

1. `std.control.var.ref` は公開 abstraction として維持する。
2. compiler が生成した local mutable var だけを、内部表現として `LocalRefCell` に置き換える。
3. `LocalRefCell` は escaped ref value として持ち運べる。
4. ただし continuation capture 時には local cell state を snapshot し、multi-shot resume では snapshot から fork した cell 群で実行する。
5. generic / user-defined / file / projected ref は今の `get` / `update_effect` / `ref_update` protocol を truth surface として残す。
6. 最初から全置換せず、feature flag と compare oracle で段階導入する。

目標は「`for` + local mutable ref` の hot path を、record field selection + `update_effect()` + `ref_update` + local `get` + local `set` + catch/resume の連鎖から外す」ことである。`for` そのものの最適化はその後でよい。現在の測定では `for_no_ref` が数 ms、`for + ref` が約 2 秒なので、まず local ref representation を直すのが支配的である。

---

## 1. `LocalRefCell` は正しいか

正しい。ただし、採用してよいのは次の意味での `LocalRefCell` だけである。

```text
LocalRefCell = compiler-generated local var act の等価な VM 内部表現
```

採用してはいけないのは次である。

```text
LocalRefCell = どこからでも見える普通の共有 mutable box
```

現在の lowering は、local mutable var を次のように扱っている。

```text
let #x = init
let &x = synthetic_var_act::var_ref()
synthetic_var_act::run #x {
  body
}
```

この形は遅いが、意味論上はかなり強い情報を持っている。

- local var act は compiler-generated で hygienic である。
- local state の lifetime は `run` の dynamic extent に対応する。
- `get` / `set` は普通の effect operation として handler に捕まる。
- `ref.update` は `ref_update` effect を使って projection chain を更新できる。

したがって VM は、任意の `ref` を勝手に cell 化してはいけない。最適化対象は「compiler が作った synthetic local var act に由来する ref」だけに限定するべきである。

---

## 2. captured continuation / multi-shot resume での意味論

ここが一番重要である。推奨する意味論は **snapshot/fork semantics** である。

### 通常実行

`my $x = v` は fresh な logical local cell `c` を作る。

```text
$x              => read c
&x = v2         => write c v2; return ()
&x.update(f)    => old = read c; new = f old; write c new; return ()
&x              => ref value pointing to c
```

`f old` の評価は、現行の `ref.update` と同じ dynamic context で起こす。つまり marker / provider / handler boundary を飛ばさない。

### continuation capture

continuation を capture するとき、その continuation から到達可能な `LocalRefCell` の値を snapshot に含める。

```text
StoredContinuation {
  frames,
  marker_scopes,
  local_cell_snapshot: [(cell_handle, value)]
}
```

「到達可能」は少なくとも次を含む。

- continuation frame 内の `Value`
- closure env 内の `Value`
- active local-cell scope に登録された cell
- record / tuple / list などの中に入った escaped local ref

最初の実装は少し保守的に「active local-cell scope にある cell をすべて snapshot」でもよい。capture は通常 loop hot path ではないので、ここで単純さを優先する価値が高い。

### resume

captured continuation を resume するときは、snapshot から fresh な cell 群を作り、captured frames/env 内の local cell handle を fresh handle に remap してから実行する。

```text
capture at state x = 10
resume k ()  => branch A starts with x = 10
resume k ()  => branch B starts with x = 10
```

branch A の中で `x = 20` になっても、branch B は `x = 10` から始まる。

これは current `var.run` lowering に最も近い保守的な意味論である。state を handler recursion の引数として持っている現在のモデルでは、multi-shot continuation を再利用するときに「以前の resume が変えた cell を次の resume が見る」と考えるより、「capture 時点の handler state から再開する」と考える方が安全である。

### one-shot optimization

後から one-shot が証明できる場合だけ、fresh remap を省いて既存 cell を reuse してよい。ただしこれは optimization であり、observable semantics は snapshot/fork のままである。

```text
semantic rule: snapshot/fork
optimization: if one-shot proven, destructive reuse is allowed
```

逆に、raw shared-cell semantics を既定にしてから「multi-shot のときだけ何とかする」は避けるべきである。これは高確率で小さな canary をすり抜け、後で handler と nondet の組み合わせで壊れる。

---

## 3. 実装形態の推奨

一番よい形は **new control IR node + tagged runtime ref representation** である。

### 推奨 IR

source / type inference 側は、当面 current lowering を大きく壊さなくてよい。ただし lowerer が synthetic local var act を作るタイミングで、control lowering に渡せる metadata を残す。

その metadata を使って、control IR へ次のような node を出す。

```rust
enum ControlExpr {
    LocalCellScope {
        slot: LocalCellSlot,
        init: ExprId,
        ref_binding: LocalDef,
        body: ExprId,
    },
    LocalCellGet {
        slot: LocalCellSlot,
    },
    LocalCellSet {
        slot: LocalCellSlot,
        value: ExprId,
    },
    LocalCellMakeRef {
        slot: LocalCellSlot,
    },
    LocalCellUpdate {
        slot: LocalCellSlot,
        function: ExprId,
    },
}
```

実際の Rust の enum 名は既存設計に合わせてよい。重要なのは「runtime が偶然の AST shape や record field name を覗いて判断しない」ことである。

### なぜ runtime pattern specialization だけでは弱いか

`var_ref` / `run` の既存 source shape を runtime で認識する案は魅力的だが、避けたい。

理由は次である。

- std の実装 shape 変更に弱い。
- user-defined ref record と compiler-generated local var ref の区別が曖昧になる。
- handler hygiene / marker / provider の根拠が「たまたまこの形だった」になりやすい。
- projection ref や escaped ref を拡張すると、後から special case が増殖する。

ただし、DefId / synthetic act metadata に基づく **compiler-generated local var act の specialization** はよい。これは string matching ではなく、lowerer が作った内部事実に基づく変換である。

---

## 4. escaped ref の表現

escaped `&x` は `Value::Ref` 系の tagged value として表すのがよい。

```rust
enum RefRepr {
    LocalCell(LocalCellHandle),
    Projection {
        base: Rc<RefRepr>,
        lenses: Rc<[LensStep]>,
    },
    Generic(Value),
}

enum Value {
    Ref(Rc<RefRepr>),
    // existing variants...
}
```

あるいは既存の `Value::Record` との互換を保ちたいなら、`Value::Ref` を直接公開せず、`select("get")` / `select("update_effect")` 時に intrinsic closure を返す実装でもよい。

重要な点は、`&x` が closure や record に入っても、次の情報を失わないことである。

```text
this is a compiler-generated local ref backed by LocalCellHandle
```

これにより、次が可能になる。

- `$x` は direct get。
- `&x = v` は direct set。
- `&x.update(f)` は direct update。
- `foo(&x)` の中で generic `r.get()` が呼ばれても、receiver が `LocalCell` なら fast path。
- receiver が user ref / file ref / generic record なら既存 protocol に fallback。

`std.control.var.ref` は公開型として維持する。VM 内部で `LocalCell` を持っていても、型上は `ref e a` として扱える必要がある。

---

## 5. projected refs と `ref_update`

projected refs は `LocalCell` と相性がよいが、ここで `ref_update` protocol を壊してはいけない。

推奨表現は lens chain である。

```rust
enum LensStep {
    RecordField(FieldKey),
    TupleIndex(usize),
    ListIndex(usize),
    StringRangeOrChar(...),
}
```

`Projection { base, lenses }` の操作は次のように定義する。

```text
projection.get():
  root = base.get()
  return lenses.get(root)

projection.set(v):
  base.update(root => lenses.set(root, v))

projection.update(f):
  base.update(root => {
    focus = lenses.get(root)
    new_focus = f(focus)
    lenses.set(root, new_focus)
  })
```

base が `LocalCell` なら、`base.update` は direct cell update に落とせる。base が generic ref なら、現在の `update_effect` + `ref_update` protocol に fallback する。

この構造にすると、次の両方が守れる。

- `&xs[i] = v` のような known projection は速い。
- user-defined ref や custom projection は今まで通り `ref_update` で動く。

`ref_update` は消すのではなく、generic truth surface として残す。VM-known pure structural projection だけを direct lens update に置き換える。

---

## 6. staged implementation plan

### Stage 0: baseline と semantic canary を固定する

コード変更前に、性能と意味論の baseline を固定する。

最低限の baseline workload:

```text
bench/nondet_20_discard.yu
bench/loop_recursive_20_discard.yu
bench/loop_recursive_sum_20_discard.yu
bench/loop_for_no_ref_20_discard.yu
bench/loop_for_sum_ref_20_discard.yu
bench/loop_for_20_discard.yu
examples/showcase.yu
```

追加したい counters:

```text
local_ref_generic_get_requests
local_ref_generic_set_requests
local_ref_generic_update_effect_calls
local_ref_ref_update_requests
local_cell_allocs
local_cell_direct_get_hits
local_cell_direct_set_hits
local_cell_direct_update_hits
local_cell_projection_get_hits
local_cell_projection_set_hits
local_cell_projection_update_hits
local_cell_generic_fallbacks
local_cell_snapshot_captures
local_cell_snapshot_cells
local_cell_resume_forks
local_cell_resume_reuses_one_shot
```

rollback point:

```text
No behavior change. counters only.
```

### Stage 1: `LocalCellHandle` と `RefRepr` を入れるが、まだ lowering しない

runtime に `LocalCellHandle` と `RefRepr` を追加する。手書きの internal test で direct get/set/update だけ動かす。

この段階では通常の Yulang program はまだ旧 path を通る。

rollback point:

```text
Value representation change を feature flag で未使用に戻せる。
```

### Stage 2: continuation snapshot/remap を先に実装する

`StoredContinuation::capture` に local cell snapshot を追加する。

最初は安全寄りでよい。

- capture 時に active local cells を全部 snapshot。
- resume 時に fresh cells を作る。
- captured continuation frames/env の中の `LocalCellHandle` を fresh handle に remap する。
- multi-shot resume は毎回 fresh fork。

この stage が入る前に `LocalRefCell` を default 有効化しない方がよい。

rollback point:

```text
Local cell lowering はまだ off。
既存 program の behavior/perf が変わらない。
```

### Stage 3: compiler-generated local var だけを `LocalCellScope` へ lowering する

`lower_local_var_binding` が持っている synthetic var act 情報から、control lowering で `LocalCellScope` を生成する。

ここで重要なのは、source 名や std 関数名の文字列一致ではなく、compiler が作った synthetic var act の内部 ID を根拠にすることである。

最初に direct 化するもの:

```text
my $x = init
$x
&x
&x = value
```

まだ `&x.update(f)` と generic `r.update(f)` は fallback でもよい。

期待値:

```text
loop_for_sum_ref_20_discard:
  2s class から for_no_ref と同じ桁へ落ちる可能性が高い
```

rollback point:

```text
LOCAL_REF_CELL_LOWERING_ENABLED=false で旧 lowering へ戻る。
```

### Stage 4: `RefSet` fast path

`RefSet` frames で reference value が次なら direct set にする。

```text
RefRepr::LocalCell(_)
RefRepr::Projection { base: LocalCell-capable, lenses: VM-known structural lenses }
```

generic `Value::Record` ref は触らない。

この stage で、assignment は `update_effect()` を呼ばなくなる。ただしこれは observable な `ref_update` を消しているのではない。current assignment machinery が内部で捕まえていた constant update を、同じ意味の direct set に置き換えるだけである。

rollback point:

```text
LOCAL_REF_FAST_REFSET_ENABLED=false
```

### Stage 5: local `get` / `update` method fast path

`select("get")` / `select("update_effect")` / `std.control.var.ref.update` の呼び出しで receiver が `LocalCell` なら fast path する。

ただし `ref.update` の評価順序を守る。

```text
old = read cell
new = apply f old   // same marker/provider/handler context
write cell new
return ()
```

`f old` が request を出した場合は、write は continuation frame として後続に置く。つまり「先に write してから f の effect を処理する」形にしてはいけない。

rollback point:

```text
LOCAL_REF_FAST_UPDATE_ENABLED=false
```

### Stage 6: projected ref direct update

list / string / record / tuple projection を `LensStep` として tagged ref にする。

最初は record field と tuple/list index だけでもよい。string は UTF-8 boundary、grapheme、byte index の仕様が絡むなら後回しでよい。

rollback point:

```text
LOCAL_REF_FAST_PROJECTION_ENABLED=false
```

### Stage 7: default 有効化

次の条件を満たしてから default on にする。

```text
- compare-control parity が通る
- adversarial corpus が通る
- local ref continuation canaries が通る
- projected ref canaries が通る
- representative local-ref loop が 2s class から脱出している
- fallback counters が説明できる
```

---

## 7. 追加する invariants / tests

### Basic local ref tests

```text
- my $x = 0; $x == 0
- &x = 1; $x == 1
- &x.update(\v -> v + 1); $x == 2
- shadowed local vars are independent
- two local refs in same scope are independent
- local ref captured by closure inside same dynamic extent works
- local ref stored in record/list and read/written later works
```

### Generic ref tests

```text
- function takes r: ref e int and calls r.get()
- function takes r and calls r.update(...)
- local cell ref passed to generic function uses same observable behavior
- user-defined ref record still uses get/update_effect path
- file ref does not become LocalCell
```

### Projection tests

```text
- record field ref get/set/update
- list element ref get/set/update
- nested projection: &record.field[i]
- projection update function performs an effect
- projection update function captures/resumes continuation
- out-of-range behavior is identical to current runtime
```

### `ref_update` protocol tests

```text
- generic projected ref still uses ref_update
- direct LocalCell assignment does not leak ref_update to outer user catch
- user custom update_effect that emits ref_update still works
- nested projection updates only focused subvalue
```

### continuation / multi-shot tests

この領域は old lowering と new lowering の比較を oracle にするのがよい。期待値を人間が決め打ちするより安全である。

追加したい canary の形:

```text
- mutate local ref, capture continuation, resume once
- mutate local ref, capture continuation, resume twice
- two nondet branches mutate same local ref
- branch A mutation does not leak into branch B unless current old lowering also leaks
- continuation returns closure containing &x; closure call behavior matches old lowering
- continuation returns record containing &x; later projection/update behavior matches old lowering
```

特に次の property を見る。

```text
capture state = S
resume k first time starts from S
resume k second time starts from S again
first resume mutations do not silently become second resume initial state
```

もし old lowering が別の結果を示すなら、old lowering を truth として合わせるべきである。ここは推測で決めない。

### hygiene / marker / provider tests

```text
- local cell fast path does not catch foreign handler operations
- direct get/set does not create or remove marker frames for unrelated effects
- provider boundary grant/miss behavior is unchanged
- same operation short name in different act does not collide
- synthetic var act is not recognized by source name string
- fallback path preserves handler boundary and callback marker semantics
```

---

## 8. smaller near-term optimization

安全に近い短期最適化はあるが、順番が大事である。

推奨する短期最適化:

```text
LocalCellScope を入れた後に、assignment-only RefSet fast path を入れる。
```

つまり、`&x = value` のときだけ、`RefRepr::LocalCell` に対して direct set する。これは `loop_for_sum_ref_20_discard` にかなり効くはずである。

避けたい短期 patch:

```text
現在の handle_ref_set_result 内で、たまたま ref_update::update が来たら assigned value で downstream patch する
```

これは attractive だが、層が悪い。`ref_update` は projection protocol の一部なので、後段で雑に潰すと custom ref / nested projection / effectful update function で壊れやすい。

もう一つの短期案として、`var_ref().update_effect` の closure shape を runtime で見て `get` を省く案もある。ただしこれも source shape 依存になりやすい。やるなら、shape recognition ではなく compiler-generated metadata から `RefRepr::LocalCell` を作る方がよい。

---

## 9. std `for` optimization は後でやる

local ref が直った後で、`for` も最適化する価値はある。

現在の測定では、pure recursive loop が約 1.5ms〜1.9ms、`for_no_ref` が約 6ms なので、`for` にも 3〜4 倍程度の余地がある。ただし `for + local ref` の 2 秒問題とは別物である。

安全な route は次である。

1. local ref fast path を default on にする。
2. `for_no_ref` と `for_sum_ref` の新 baseline を取り直す。
3. `std.control.loop.for_in` の DefId に基づき、range/list iterator だけ `ForInRange` / `ForInList` control IR にする。
4. body callback は最初は通常の function application で呼ぶ。
5. marker/provider/handler scope を通常 call と同じように閉じる。
6. labeled break/continue がある場合は、専用 canary が通るまで fallback。
7. その後で callback inline / direct body executor を検討する。

避けるべき route:

```text
- source-level for body を文字列や AST shape で special-case
- body callback の effect を無視して Rust loop に変換
- label / break / handler boundary を shortcut
- local ref 問題が残ったまま for だけ最適化して成果に見せる
```

---

## 10. option ranking

| option | semantic risk | expected gain | implementation size | fit with algebraic effects | recommendation |
| --- | --- | --- | --- | --- | --- |
| New control IR `LocalCellScope` + `RefRepr::LocalCell` + continuation snapshot/fork | Low to Medium | Very High | Medium to Large | High | Best long-term route |
| Compiler-generated synthetic var act metadata を control lowering で intrinsic 化 | Medium | Very High | Medium | High | Good transition route |
| Assignment-only `RefSet` fast path for `LocalCell` | Low after LocalCell exists | High for current 2s case | Small to Medium | High | Good early win |
| Fast generic `r.get()` / `r.update(f)` for `LocalCell` receiver | Medium | High | Medium | Medium to High | Do after assignment fast path |
| VM-known `Projection` lens chain over `LocalCell` | Medium | Medium to High | Medium | High if fallback preserved | Do after base LocalCell |
| Existing `var_ref/run` source-shape runtime specialization | Medium to High | High | Medium | Medium to Low | Avoid unless metadata-based |
| Raw shared heap cell with no continuation snapshot | High | Very High | Small | Low | Avoid |
| Optimize std `for` first | Low | Medium | Medium | High | Do later |
| Benchmark/file-path/source-name special casing | Very High | Misleading | Small | Very Low | Never do |

---

## 11. option that looks attractive but should be avoided

### Raw `Rc<RefCell<Value>>`

これは最も tempting だが、multi-shot continuation で危険である。

```text
capture k at x = 0
resume k -> x becomes 1
resume k again
```

second resume が `x = 1` から始まるのか、`x = 0` から始まるのかは、言語意味論そのものである。現在の handler-based lowering と整合させるなら、`x = 0` から始める方を既定にすべきである。

### `ref_update` を後段で握りつぶす

assignment のために内部 `ref_update` を使っているからといって、`ref_update` 全体を optimization target として雑に消すのは危ない。projection update の焦点移動 protocol でもあるためである。

### record field name による ref 判定

`get` と `update_effect` という field がある record を見て local ref と判定してはいけない。public abstraction と user-defined abstraction を壊す。

### provider / marker shortcut と混ぜる

local cell optimization は state representation の最適化であって、handler selection や provider grant/miss の最適化ではない。ここを混ぜると、既存の handler hygiene 修正を巻き戻しやすい。

---

## 12. 実装上の最終形

最終的には次の構成がよい。

```text
source syntax:
  my $x = init
  $x
  &x

inference-level meaning:
  still compatible with std.control.var.ref and local var act abstraction

control IR:
  LocalCellScope / LocalCellGet / LocalCellSet / LocalCellMakeRef / LocalCellUpdate

runtime value:
  Value::Ref(RefRepr::LocalCell(handle))
  Value::Ref(RefRepr::Projection { base, lenses })
  Generic ref fallback remains existing record/function/effect protocol

continuation:
  StoredContinuation captures local cell snapshot
  multi-shot resume forks fresh cells
  one-shot resume may reuse only as an optimization

fallback:
  any non-VM-known ref uses get/update_effect/ref_update exactly as before
```

この形なら、2 秒級の local ref update path を cause-side で取り除ける。かつ、Yulang の algebraic effects / handlers / effect rows / hygiene を「実装都合で弱める」方向にはならない。

最初の実用上の成功条件は次で十分である。

```text
loop_for_sum_ref_20_discard: 2s class -> single-digit or low-10ms class
loop_for_20_discard:        2s class -> list allocation cost + for overhead class
nondet_20_discard:          regressionなし
showcase:                   regressionなし
adversarial corpus:          regressionなし
continuation canaries:       old lowering と一致
```

その後で `for` を direct iterator IR に落とすと、recursive loop との差を詰められる。順番は local ref first, `for` second がよい。