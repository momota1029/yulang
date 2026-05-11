読んだ範囲とコード確認を踏まえると、次の実装担当 LLM に渡すべき結論はこうだねぇ。

**write17 の pre-force 方針は、そのまま再有効化しない。次は `Return(Thunk)` pre-force を詰めるより、既存の `continue_return_frames` 経由を前提にして、`std::undet.once` の resumption replay / return frame chain / threshold truncate を event-by-event で追い、`cps:3` へ進む瞬間を潰すのが本筋**だよ〜。

理由はかなりはっきりしている。write17-report で、pre-force helper は thunk body を `fold_impl` の `current_function` で走らせてしまい、`each` で install された `H_sub` の `escape_owner_function` と一致しない。その結果、`ScopeReturn` が root へ escape する。既存の non-pre-force flow は、`continue_return_frames` で `each cont 12` に乗り換えるから `current_function = each` になり、`H_sub` を正しく resolve できる。ここは write17-report の観察が決定的だねぇ。

---

# まず全体像

`notes/todo` は Yulang の広い backlog で、現在作業は `tasks/current.md` に寄せる運用になっている。Native Backend track は effect-aware CPS lowering / CPS repr / Cranelift へ伸びる主線で、`std::undet` 系はその中の early target として扱われている。

`std::undet.once` は設計ノート上でも「最初の実装対象」ではなく統合ターゲット扱いになっていて、branch/reject、multi-shot resumption、resumption queue、recursive handler loop、`fold` / `sub::return`、handler/guard snapshot、handler boundary をまたぐ thunk callback が全部乗っている難物だと明記されている。

標準ライブラリ側の形はこうだねぇ。`each` は `sub::sub` の中で `xs.fold` を呼び、callback 内で `branch()` が true なら `sub::return x`、false なら unit、fold 後に `reject()` する。`once` は `loop x []` で handler を張り、`branch(), k -> loop(k true, queue + [k])`、`reject()` なら queue から `k false`、value なら `just v` を返す。

`fold_impl` は `empty -> z`, `leaf x -> f z x`, `node(left,right) -> fold_impl(right, fold_impl left z f, f)` という再帰形だから、callback の効果・Thunk-return・post-call frame が絡みやすい。今回の `each [1,2,3]` 系で frame chain が複雑になるのは自然だよ〜。

---

# ここまでの実装履歴の読み

## write15

write15 では targeted lowering が入った。`std::list::fold_impl`、`std::undet::undet::each`、`std::undet::undet::once` を `higher_order_helper` として扱い、その中で thunk-return っぽい apply/direct call を `EffectfulApply` / `EffectfulCall` にする方針だねぇ。さらに `return_frame_threshold` が入って、handler scope からの non-local exit で handler install 後の return frames を捨てる設計になった。

この時点で通常テストと write12/13 の local tests は通り、`debugs_std_undet_once_skip_eval_layers` は `cps:0 vs vm:2` から `cps:3 vs vm:2` へ進んだ。これは完全失敗から「探索は走るが 2 で止まらず 3 へ行く」状態へ進んだ、という大事な変化だねぇ。

## write16

write16 では `std::undet::undet::once` 内の closure apply を強制的に `EffectfulApply` 化し、`EffectfulApply(Resumption)` の frame order も修正した。`continue_return_frames` が末尾から pop するため、post-call frame を末尾に置くと captured continuation より先に post frame が走る、という罠を直した形だねぇ。

それでも `debugs_std_undet_once_skip_eval_layers` は `cps:3 vs vm:2` のまま。write16-report の重要観察は「branch Perform が 1 回しか出ていない」「x=2 の branch Perform が起きていない」こと。ただし、write17-report を読むと、この観察をそのまま「F_each_post が見えていないから」と断定するのは少し危ない。write17 で既存 flow は `H_sub` resolve までは正しくやっていると確認されているからだねぇ。

## write17

write17 の pre-force 実験は、発想自体は「Return(Thunk) が post frame を早く consume しすぎるなら、その前に Force しよう」というものだった。でも実装してみると、thunk body の `current_function` が `fold_impl` になり、`each` の handler frame が持つ `escape_owner_function = each__mono1` と一致しない。`handle_scope_return` は owner check を要求するので、`ScopeReturn` が propagate して root へ escape する。

CPS evaluator 側では `eval_continuations` が handler frames を inherited 化し、`resume_continuation` はそれをしない。`resume_continuation` は `continue_return_frames` で復元した frame の inherited / non-inherited 状態を保つために必要な入口だねぇ。`handle_scope_return` は non-inherited handler だけを探し、さらに `escape_owner_function == current_function` を要求する。

ここからの結論はこれ。

**`handle_scope_return` の owner check を緩めない。pre-force helper をそのまま有効化しない。`continue_return_frames` で function context を乗り換える既存構造を壊さない。**

`target` の continuation id は install 元 function の continuation id だから、`fold_impl` の eval loop で `current = target` にするのは意味的に危ない。cont id がたまたま整数で一致しても、所属 function が違うなら別物だよ〜。

---

# 実装担当 LLM への方針

## 主作業

`debugs_std_undet_once_skip_eval_layers` を `CPS eval: 2 / VM: 2` に一致させる。

ただし、最初に直す場所を決め打ちしすぎない。次の trace を増やして、**どの event で 2 が失われ、3 に流れるか**を確定する。

## 触らないもの

* `handle_scope_return` の owner check を緩めない
* write14 の `initial_frame_count` 設計を大改造しない
* `return_frame_threshold` を証拠なしに外さない
* global に `ApplyClosure` 全体を `EffectfulApply` 化しない
* global に `ForceThunk` 全体を `EffectfulForce` 化しない
* Cranelift backend を同時に直そうとしない
* write17 の pre-force helper を active path に戻さない

---

# 実行手順

## Step 0: baseline を固定する

まずこの 4 本を作業前に走らせる。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待する現状。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => cps:3 vs vm:2
```

ここが違うなら、今回の調査へ進む前に差分を切り分ける。

---

## Step 1: write17 pre-force path を inactive のまま確認する

`cps_eval.rs` に残っているはずの helper は、そのまま dormant / debug-only にしておく。

* `return_frame_immediately_forces_param`
* `force_returned_thunk_before_frame_consumption`
* Return trace の `value_is_thunk`

やることは、**helper が存在しても Return terminator から active に呼ばれていないことを確認する**だけ。

理由は上の通り。pre-force を fold_impl 文脈で走らせると `ScopeReturn` の owner check に当たる。ここを無理に突破すると、function-local continuation id の所有関係を壊す。

---

## Step 2: trace を「値」ではなく「frame chain」中心に増やす

既存 trace は `Perform` / `Return` / `EffectfulApply` にある。次は resumption replay の chain を見るため、以下を追加する。

### `CpsTerminator::Perform`

出す情報。

```text
event = Perform

function
current_cont
effect path
resume continuation
return_frames.len
initial_frame_count
active_handlers summary
captured resumption owner_function
captured resumption target
captured resumption return_frames summary
captured guard_stack summary
```

`return_frames summary` は巨大な Debug dump にしない。1 frame につきこれだけでいい。

```text
[
  {
    owner_function,
    continuation,
    owner_initial_frame_count,
    active_handlers: [(prompt, inherited, escape_owner_function, threshold)]
  },
  ...
]
```

### `CpsTerminator::EffectfulApply`

特に runtime value が `Resumption` のとき。

```text
event = EffectfulApply

function
current_cont
closure_value_kind = Closure | Resumption | Other
arg summary   // true / false / unit / int くらいは見えるようにする
resume continuation
pre_push return_frames.len
new_frames summary
resumption owner_function
resumption target
resumption return_frames summary
combined_frames summary
initial_frame_count passed to replay
```

ここで重要なのは **combined_frames の末尾が何か**。`continue_return_frames` が末尾から pop する以上、最初に走ってほしい frame が末尾にある必要がある。

### `CpsStmt::ApplyClosure`

write16 では `once` 内 apply は `EffectfulApply` 化されたはずだけど、runtime 上で `ApplyClosure(Resumption)` がまだ残っている可能性を潰す。

```text
event = ApplyClosure

function
current_cont
callable kind
arg summary
resumption target if any
adjusted_frames / combined_frames summary
```

### `continue_return_frames`

出す情報。

```text
event = ContinueReturnFrames

value summary
frames.len before
popped frame owner_function
popped frame continuation
rest.len after pop
frame.owner_initial_frame_count
owner_initial after clamp
active_handlers summary in popped frame
```

ここは特に `owner_initial_frame_count.min(rest.len())` が発動していないかを見る。write15 で clamp が入っているから、これが頻発するなら threshold truncate 後の frame ownership が崩れている手がかりになる。

### `handle_scope_return`

`Propagate` した理由を trace に出す。

```text
event = ScopeReturnDispatch

current_function
prompt
target
matched? yes/no
matched frame escape_owner_function
matched frame inherited
owner_match yes/no
return_frame_threshold
return_frames.len before truncate
return_frames.len after truncate
action = Value | JumpOrExit | Propagate
```

write17 の escape はここで `owner_match = false` だったはずだねぇ。

---

## Step 3: trace 実行

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

trace はそのままだと多すぎる可能性がある。必要なら環境変数を分ける。

```rust
fn trace_frames_enabled() -> bool {
    std::env::var_os("YULANG_CPS_TRACE_FRAMES").is_some()
}

fn trace_undet_enabled() -> bool {
    std::env::var_os("YULANG_CPS_TRACE_UNDET").is_some()
}
```

`YULANG_CPS_TRACE_UNDET=1` のときだけ `function.contains("undet") || function.contains("fold_impl") || function.contains("root")` に絞るのもありだねぇ。

---

# 判定表

trace を見て、次のどれかに分類する。

## Case A: `k false` replay の frame order が違う

症状。

```text
reject arm で k false を呼ぶ
しかし combined_frames の末尾が captured frame ではなく F_post / parent frame
または handler body の post frame が captured continuation より先に pop される
```

修正。

`EffectfulApply(Resumption)` と `ApplyClosure(Resumption)` の両方を同じ規則にする。

`continue_return_frames` が末尾 pop なら、最初に実行したい captured frames を末尾側に置く。

概念上はこう。

```text
combined_frames = parent_frames + [F_post] + captured_frames
```

ただし vector の末尾が先に pop されるので、`captured_frames` の中でも innermost frame が末尾になるようにする。

write16-report では `EffectfulApply(Resumption)` は修正済みとある。でも `ApplyClosure(Resumption)` 側、`Resume` 側、`inject_extra_handlers` 後の順序、`extra` handlers を入れた後の threshold まではまだ再確認が必要だよ〜。

## Case B: `k false` replay は正しいが、x=2 の branch Perform が起きない

症状。

```text
k false は x=1 の branch false continuation に戻る
fold は継続しているように見える
でも x=2 callback の branch Perform が出ない
```

見る場所。

* `fold_impl` の `leaf x -> f z x`
* `node(left,right) -> fold_impl(right, fold_impl left z f, f)`
* `EffectfulCall fold_impl`
* `Return(Thunk)` 後の `continue_return_frames`
* `ForceThunk` が sync stmt として走る時の `return_frames`

ここで注意。write17 の結果から、**pre-force で直接 thunk body を fold_impl 文脈で走らせるのはダメ**。やるなら trace で「どの frame が missing か」を証明してから、`continue_return_frames` と owner function 文脈を保つ設計にする必要がある。

この Case B で最初に試すべき修正は、pre-force 復活ではなく、`EffectfulCall fold_impl` が push した post frame と、fold_impl 内部の recursive `EffectfulCall` / `EffectfulApply` が作る frame の順序確認だねぇ。

## Case C: x=2 の `sub::return 2` は起きるが、最終的に 3 になる

症状。

```text
Perform sub::return payload=2 が出る
ScopeReturn も H_sub に match する
でも return_frames truncation 後に fold / each の続きが残り、
x=3 側へ進む
```

修正候補。

`return_frame_threshold` の値を疑う。ただし外さない。

確認すること。

```text
InstallHandler H_sub の時点で return_frame_threshold が何か
ScopeReturn(H_sub) match 時に同じ threshold が使われるか
truncate 前に frames.len はいくつか
truncate 後に fold continuation が残っていないか
```

`return_frame_threshold` は handler install 後に push された frames を non-local exit で捨てるための設計だから、これを消すとむしろ `sub::return` 後に fold の続きが残りやすい。

## Case D: once value arm が `just 2` を返した後、queue replay が続く

症状。

```text
once value arm v -> just v に入る
just 2 が返る
その後も queue から k false が replay される
最終的に just 3 / 3 へ上書きされる
```

見る場所。

* `once` の value arm continuation
* value arm `Return` 時の return_frames
* `return_frame_threshold` により once loop 内 frames が切れているか
* `loop(k true, queue+[k])` の post frame が value return 後に残っていないか

この場合は `once` handler の value arm が「探索成功で即終了」する extent を持てていない。`v -> just v` は std 実装上、queue を続けない意味だから、value arm の Return 後に reject arm / queue loop の rest が残るなら frame extent が壊れている。

---

# 最初に入れる修正の優先順位

## 1. frame order の統一チェック

まず `Resumption` を再開する全経路を横並びで読む。

* `CpsStmt::ApplyClosure` の `Resumption` branch
* `CpsStmt::Resume`
* `CpsStmt::ResumeWithHandler`
* `CpsTerminator::EffectfulApply` の `Resumption` branch
* `CpsTerminator::EffectfulForce` がもし使われているならそこ
* `continue_return_frames`
* `inject_extra_handlers`

write16 で `EffectfulApply(Resumption)` の frame order は直ったとあるけど、同じ規則が全 resumption replay 経路に揃っているかを確認する。ここがズレると、`once` の `k true` / `k false` みたいな queue replay でだけ壊れる。

## 2. threshold trace で `sub::return` の extent を確認

`H_sub` の `return_frame_threshold` が正しく install 時点の frame count になっていて、`sub::return` の `ScopeReturn` で handler scope 内 frames が切れているかを見る。

write17-report では、pre-force なしの既存 flow なら `H_sub` は `each` 文脈で match できる。だから次は「match できるか」ではなく、「match した後に何が残るか」を見る。

## 3. `Return(Thunk)` pre-force は最後の手

write17 helper を使うなら、最低でもこの条件が必要。

```text
- thunk body を fold_impl current_function で直接 ScopeReturn dispatch しない
- target continuation id の owner function を常に守る
- top frame の owner_function 文脈へ入る
- ただし top frame を通常 pop した場合と同じ意味を保つ
- Perform capture には必要な post frame を見せる
- plain Return で同じ top frame を二重消費しない
```

これはもう「pre-force helper」ではなく、小さな continuation scheduler だねぇ。今すぐやるには危ない。

---

# lower 側を触る条件

`fold_impl` の `MakeThunk + Return` 自体を抑制する案は、直感的には根本修正に見える。でも後手でいい。

理由。

* Thunk wrapping は effect typing / demand / handler boundary の広い意味に絡む
* `fold_impl` だけ名前ベースで special-case すると、std special-case がさらに増える
* write15/16/17 で既に evaluator 側の frame semantics が揺れているため、lower を変えると原因が混ざる
* `cps:3` は「完全に frame が無い」より replay chain の順序・extent の可能性が高い

lower 側へ行く条件はこれ。

```text
trace で以下を証明した場合だけ:
1. resumption frame order は全経路で正しい
2. return_frame_threshold も正しい
3. x=2 に進むべき captured continuation が存在しない
4. その欠落が fold_impl の MakeThunk + Return wrapper でしか説明できない
```

その場合の候補は、`higher_order_helper` の中でも `std::list::fold_impl` の thunk wrapping を抑えるのではなく、まず **「effectful callee が Thunk を返し、caller post-cont が即 ForceThunk する」形を CPS IR として明示する** 方向がよさそうだねぇ。`EffectfulForce` は IR に存在していて、コメント上もこの用途を意識している。ただし write16 の単純導入は `cps:0` に悪化したので、frame ownership と threshold を trace で固めてから再設計する。

---

# 実装担当 LLM にそのまま渡す指示文

```text
目的:
debugs_std_undet_once_skip_eval_layers を CPS eval:2 / VM:2 に一致させる。
現状は write17-report 後で cps:3 vs vm:2。

重要な現状:
- write15 で fold_impl / each / once の targeted EffectfulCall/Apply lowering と return_frame_threshold が入った。
- write16 で once 内 ApplyClosure は強制 EffectfulApply 化され、EffectfulApply(Resumption) の frame order も修正された。
- write17 で Return(Thunk) pre-force を試したが、thunk body の current_function が fold_impl になり、each で install された H_sub の escape_owner_function と一致せず ScopeReturn が escape した。
- pre-force path は disabled のままにする。
- handle_scope_return の owner check は緩めない。

作業:
1. baseline を取る。
   cargo test -p yulang-native
   cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

2. cps_eval.rs の trace を frame chain 中心に増やす。
   対象:
   - Perform
   - EffectfulApply
   - ApplyClosure
   - Resume
   - ResumeWithHandler
   - Return
   - continue_return_frames
   - handle_scope_return / dispatch_scope_return

   出す情報:
   - current function / continuation
   - return_frames.len
   - initial_frame_count
   - active_handlers の prompt / inherited / escape_owner_function / return_frame_threshold
   - resumption owner_function / target / captured return_frames summary
   - combined_frames の順序
   - ScopeReturn の owner_match / threshold truncate 前後

3. YULANG_CPS_TRACE_FRAMES=1 で debugs_std_undet_once_skip_eval_layers を走らせる。

4. trace を次の観点で分類する。
   A. k false replay の combined_frames 順序が違う
   B. k false replay 後に x=2 branch Perform が起きない
   C. sub::return 2 は起きるが ScopeReturn 後に fold/each の続きが残る
   D. once value arm が just 2 を返した後も queue replay が続く

5. 最初に修正する候補は resumption replay frame order。
   EffectfulApply(Resumption) だけでなく、ApplyClosure(Resumption), Resume, ResumeWithHandler の全経路で同じ pop 順になっているか確認する。
   continue_return_frames は末尾から pop するので、captured continuation frames が handler post frame より先に pop される順序にする。

6. 次に return_frame_threshold を trace で確認する。
   H_sub install 時の return_frames.len が threshold になっているか。
   sub::return の ScopeReturn match 時に handler install 後の frames が truncate されるか。
   threshold は外さない。

7. write17 の pre-force helper は active にしない。
   owner check を緩めない。
   fold_impl current_function で each の escape continuation を解決しない。

8. lower 側の fold_impl MakeThunk+Return 抑制は最後の候補。
   frame order と threshold が正しいことを trace で証明してから検討する。

成功条件:
- cargo test -p yulang-native が pass
- debugs_local_choice_caller_rest_eval が pass
- debugs_local_choice_callback_rest_eval が pass
- debugs_std_undet_once_skip_eval_layers が CPS eval:2 / VM:2
- trace 上、2 が生成された後に 3 へ進む余分な replay / frame consumption が消えている
```

---

# 私のおすすめ実行順

1. **pre-force を触らず、trace を増やす**
2. **resumption replay の全経路を横並びで frame order audit**
3. **`sub::return 2` が起きるかどうかを確認**
4. 起きるなら **threshold / truncate 修正**
5. 起きないなら **fold_impl replay chain / missing post frame を追う**
6. それでも説明できないときだけ **EffectfulForce 再設計 or lower 側 thunk wrapper 抑制**

一番危ない修正は、`handle_scope_return` の owner check を緩めること。これは一見 escape を消すけど、function-local continuation id の所有関係を壊す可能性が高い。ここは止めた方がいいよ〜。
