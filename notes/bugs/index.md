# notes/bugs index (2026-05-16 更新)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。

## 作業中メモ（2026-05-15 round-5 / 未コミット WIP）

round-5 の 5 snippet は、手元 WIP ではいったん全て期待出力まで到達した。

```text
role_method_in_for_body_pattern.yu                 -> [0] 4
handler_fn_missing_join_evidence.yu                -> [0] ["a"]
record_field_value_selection_selector_shape.yu     -> [0] true
callback_list_index_raw_type_stuck.yu              -> [0] 0
wrap_does_not_traverse_from_chain.yu               -> [0] "err: not_found"
```

ただし、この WIP は既存 VM 回帰を壊すので、まだ解決済みに移さない。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_
```

で `vm_runs_std_undet_once_and_sub_return_roots` が落ちる。最小化すると
`std::undet.each` / `.once` 内の `std::range::fold` callback が絡む。

```yulang
use std::undet::*

({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
```

現在の WIP では `principal_unify` 後に `a` / `b` / `c` が一度 `int` まで
固まるが、その後の role method selection で receiver が `Tuple([])` /
`unit` 側へ崩れ、`expected (), got int` になる。直接の失敗点は
`std::range::fold_from` / `fold_ints` の callback effect projection と、
そこから先の role receiver projection の食い違いに見える。

手元で試した方向:

- `handler_fn_missing_join_evidence` は、`handle` の join evidence が無い時だけ
  arm から消費 effect を読み、body が未精密な local value なら thunk expected
  を与えると通る。ただし広げすぎると `undet.each` の body value を `unit`
  に潰す。
- `callback_list_index_raw_type_stuck` は、list element へ function value を
  入れる時に effectful callback の境界を保持すれば通る。ただし local function
  value を wrapper 化する範囲を広げると `range.fold` の callback shape に
  干渉する。
- `principal_unify` / `types/substitution.rs` では function の `param_effect` /
  `ret_effect` を value precision ではなく effect precision で merge する必要が
  ある。片側だけ直すと `Never` が勝って `std::range::fold` の effect var が潰れる。

次に見る場所:

- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `project_closed_value_substitutions_from_type`
  - `project_closed_substitutions_from_type`
  - role impl candidate の receiver projection
- `crates/yulang-runtime/src/types/substitution.rs`
  - `merge_projected_type_precision` の function effect slots
- `crates/yulang-runtime/src/lower/lowerer.rs`
  - `Handle` lowering の missing join evidence fallback
  - local callback value の effect boundary preservation

現時点の判断:

- snippet 5件の表面だけを通す patch は作れる。
- `std::undet.each` / `.once` の既存回帰は 2026-05-15 に修正済み。
  full apply-spine の principal plan がある場合は、内側の単一 apply evidence
  由来の古い `unit` substitution で上書きしない。候補が open だけの
  `unit` substitution も concrete な根拠として扱わない。
- 次は round-5 snippet の regression test を戻して、同じ principal
  elaboration 経路で壊れないか確認する。

## 現在の未解決（2026-05-15 round-5）

round-5 の非 native snippet は 2026-05-16 時点で全て再現しない。新しい
非 native regression が出たらここへ戻す。

## 現在の未解決（2026-05-15 round-6 / `yulang run --native` との差分）

VM (`yulang run --interpreter`) と native (`yulang run --native`) で結果が
食い違うものを集める。既存の `native_*.yu` snippet と並べる。

### CPS lowering 未対応 / 値違い

- [`native_cps_lowering_unsupported.yu`](native_cps_lowering_unsupported.yu)
  — labelled `for` の bare effect operation
  (`#loop_label:outer##with0::...`) が CPS lowering 未対応で
  `failed to compile native effects object` で止まる。VM では通る。handler arm
  の `if` guard は 2026-05-16 に native CPS lowering へ追加済み。
  `#loop_label` 側は bare effect operation を closure 化するだけでは足りない。
  `for` callback 内の var handler 更新が native で潰れる問題は 2026-05-16 に
  `runs_var_update_in_for_loop_through_cps_repr` で regression 化して一度解消済み。
  ただし下の prompt-exit WIP では JIT 側だけ再発し、期待 `4` に対して `0` になる。

- `std::undet` の native CPS 回帰は 2026-05-16 時点で二系統残っている。
  `(branch()).list` は native CPS eval まで進むが `[[1], [0]]` になり、value arm
  の扱いが list で一段多い。open range + `guard` の `.once` は
  `:just :just 3` になり、queued resumption 成功時に recursive `once` の value arm
  と元の `once` の value arm が両方走る。handler snapshot から捕捉 handler だけを
  抜く実験では `for` callback var handler が壊れ、handler 境界 frame を切る実験では
  `guard` 後続または fold 後続が落ちるため、return-frame segment と handler value arm
  境界を分けて扱う必要がある。

  2026-05-16 の再整理: これは「handler frame を stack から消す」問題ではなく、
  handler prompt の内側の subcontinuation だけを捕まえる問題。shallow handler の
  resumption は `k = λx. E[x]` であり、`λx. value_arm_P(E[x])` ではない。
  現在の CPS eval / repr は ordinary return frame、handler lookup frame、
  handler value arm / escape target を `return_frame_threshold` と
  `active_handlers` snapshot で間接的に表しているため、runtime 側だけで
  suffix を切ったり handler を filter したりすると、`.once` の二重 value arm は残るか、
  `for` / var handler 更新の install scope を壊す。次の修正は明示的な
  `PromptBoundary(P)` / `PromptExit(P)` / `EscapeTarget(P)` 相当の frame model を
  CPS eval と CPS repr に入れ、`capture(P)` が P より内側の ordinary segment だけを
  保存する形に寄せる。

  2026-05-16 WIP: `PromptExit(P)` 相当を `CpsStmt::InstallHandler { value, escape }`
  と return frame の `prompt_exit` metadata として入れると、次は通る。

  ```bash
  cargo test -q -p yulang-compile runs_simple_undet_list_through_cps_repr -- --nocapture
  cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr -- --nocapture
  ```

  ただし同じ WIP で `runs_var_update_in_for_loop_through_cps_repr` の JIT 部分が
  `["0"]` になって落ちる。CPS eval / repr eval までは通っていて、JIT の
  `route_scope_return_i64` が prompt 1 の frame-walk で外側の var/for handler
  escape へ飛び、`Global` abort として caller chain を止めている。次は
  `ScopeReturn` の frame-walk 後に JIT が eval/repr と同じ「一段ずつ戻る」
  非局所 return を表せているか、`ResumeWithHandler` の env overlay と合わせて見る。

- `(each [1, 2, 3]).list` / `.logic` / nested `.once` などは native の前に
  runtime lowering で `branch result type mismatch: expected unit, got std::bytes::bytes`
  になる。`check` は通るので、型推論ではなく principal core から runtime IR へ
  落とす段階の join evidence / effectful branch result の問題。`std::undet.each`
  内の `if branch() { sub::return x } else ()` が `join[unit]` として出ている一方、
  runtime lowering が true branch の actual を concrete な `std::bytes::bytes` と見ている。

## 解決済み（2026-05-14 時点で再現せず）

- [`native_handler_result_display_silent_abort.yu`](native_handler_result_display_silent_abort.yu)
  — 2026-05-16 に native CPS JIT の `ScopeReturn` routing を修正した。
  handler escape continuation が見つかった後の値を `Global` abort にせず、
  `propagate_at_threshold = false` の scoped abort として caller chain を止める。
  自己再帰 shallow handler から返った値に `.show` を当てる例は VM / native
  とも `before show / 99 / after show` を出す。
- [`native_cps_lowering_unsupported.yu`](native_cps_lowering_unsupported.yu) の
  handler guard 部分
  — 2026-05-16 に effect handler arm の guard を native CPS lowering で扱う
  ようにした。同じ effect の arm を一つの handler entry 内で順に試し、
  pattern / guard が失敗したら次 arm へ fall through する。`log::put n, k if
  n > 0` の再現は native で `()`。
- [`native_sub_for_return_int_value_garbled.yu`](native_sub_for_return_int_value_garbled.yu)
  — 2026-05-16 に native CPS の `perform_finish_escaped` 経路を修正した。
  already-escaped handler arm の結果を cross-eval 時にもう一度 `ScopeReturn` へ包むと、
  `sub:` の戻り値が後続継続まで進んだ値として再配送されていた。`sub` 内の
  `for` body から `return` し、その値を `1 + r` で使うケースは VM / native とも
  `2`。
- [`if_no_else_branch_type_mismatch.yu`](if_no_else_branch_type_mismatch.yu)
  — 2026-05-16 に `else` なし `if` を statement-like に下げるようにした。
  then branch は効果のために実行されるが値は捨てられ、式全体は `()` を返す。
  `if true: 1` は VM で `()` として通る。明示的な `else: ()` は通常の branch
  join のままなので、非 unit branch との不一致は従来通り型エラー。
- [`nested_for_return_effect_mismatch.yu`](nested_for_return_effect_mismatch.yu)
  — 2026-05-16 に runtime lowering / validate 側の thunk effect 検査を調整し、
  apply evidence 由来の residual effect を過剰に弾かないようにした。
  `sub:` 内の nested `for` から `return` する形は VM で `[0] 1`。
- [`role_method_in_for_body_pattern.yu`](role_method_in_for_body_pattern.yu)
  — 2026-05-16 時点で VM `--print-roots` が `[0] 4` を返し、再現せず。
- [`handler_fn_missing_join_evidence.yu`](handler_fn_missing_join_evidence.yu)
  — 2026-05-16 時点で VM `--print-roots` が `[0] ["a"]` を返し、再現せず。
- [`wrap_does_not_traverse_from_chain.yu`](wrap_does_not_traverse_from_chain.yu)
  — 2026-05-16 時点で VM `--print-roots` が `[0] "err: not_found"` を返し、
  再現せず。
- [`debug_role_missing_for_composite_types.yu`](debug_role_missing_for_composite_types.yu)
  — 2026-05-16 に stdlib へ `Debug` role と primitive / list / opt /
  result / tuple / record の `.debug` を追加済み。native effects の root
  pretty-print も `.debug` 投影へ寄せ、record / long tuple は host-side
  debug fallback で表示できる。残る小差は record の field separator
  (VM `{x = 1, y = 2}` / native `{x: 1, y: 2}`) のみ。
- [`native_handler_result_debug_value_garbled.yu`](native_handler_result_debug_value_garbled.yu)
  — 2026-05-16 WIP 時点で再現せず。`say` / `println` / `Debug` 整理後に再確認し、
  VM と native がどちらも `"()"` / `"after"` を出力する。以前は `act console:
  read + println` の両 operation を持つ handler の戻り値 `r` に対する
  `r.debug` が native で silent に消えていた。
- [`native_handler_result_value_collapse.yu`](native_handler_result_value_collapse.yu)
  — 2026-05-16 WIP で native effects の blocked-effect boundary dispatch を
  inactive marker で peel できるようにし、`ResumeWithHandler` sibling env を
  inner-to-outer 順で読むようにした。`collect_logs: log::put "a"` は
  native `--print-roots` で VM と同じ `["a"]`。
- [`native_value_repr_in_tuple.yu`](native_value_repr_in_tuple.yu)
  — 2026-05-16 WIP で native effects の root pretty-print を `.debug`
  投影へ寄せ、tuple 内 literal bool / unit も boxed value として構造値へ
  入れるようにした。`(true, 1, "s", ())` は native `--print-roots` で
  `(true, 1, "s", ())`。
- [`native_float_collapses_to_zero.yu`](native_float_collapses_to_zero.yu)
  — 2026-05-16 WIP で native float lane を runtime value container へ
  入れる時に boxed float へ変換し、float primitive 側へ戻す時に unbox
  するようにした。`3.14` と `[2.0]` が native で値を保つ。実機 (`yulang run
  --native --print-roots`) でも VM と同じ `3.14`。
- [`native_serial_var_double_count.yu`](native_serial_var_double_count.yu)
  — 2026-05-16 WIP 時点で再現せず。native `--print-roots` で VM と同じ
  `(11, 21)`。

- [`handler_arm_tuple_payload_pattern.yu`](handler_arm_tuple_payload_pattern.yu)
  — act operation の payload が tuple のとき、handler arm で `op (s, n), k
  -> ...` のように個別 bind すると `cannot match a tuple pattern against ?`
  で落ちていた。現在は payload pattern の構造から runtime payload 型を作り、
  `s` / `n` を個別 bind できる。
- [`record_field_value_selection_selector_shape.yu`](record_field_value_selection_selector_shape.yu)
  — native source regression を足そうとした時、`my r: {ok: bool} = ...; r.ok`
  が field value selection ではなく `:ok Record(...)` のような
  selector-shaped な値/適用として出ていた。現在は record field value
  selection が native CPS repr path でも plain value として返る。
- [`callback_list_index_raw_type_stuck.yu`](callback_list_index_raw_type_stuck.yu)
  — `my hs = [h]; ((std::list::index_raw hs) 0)()` のように callback/function
  value を list に入れて取り出すと、`index_raw` の element type `a` が
  runtime type として固まらず、型が固まった後も native 側では inner `sub`
  に捕まっていた。現在は source-shaped forced CPS repr path で VM と同じ
  `0` を返す。
- [`var_effect_serial_collision.yu`](var_effect_serial_collision.yu) —
  同じ scope で `my $a = ...; for ...; my $b = ...; for ...` と var を順に
  開くケースが、現在は `(3, 3)` を返す。
- [`typed_effect_handler_inference.yu`](typed_effect_handler_inference.yu)
  — 型引数を持つ effect (`act state 'a:`) の handler が、`[state int]`
  から `int` に specialize されて現在は通る。
- [`var_effect_leak_with_wildcards.yu`](var_effect_leak_with_wildcards.yu) —
  handler 関数の型注釈に `_` を混ぜると、`my $x = ...` で開いた局所 ref の
  `&x::get` effect が `catch` の scope を抜けて program 最外まで漏れていた。
  現在は `((), [])` を正しく返す。
- [`lambda_pattern_unbound.yu`](lambda_pattern_unbound.yu) — lambda 引数に
  destructuring pattern (`\(x, y) -> ...`, `\{ name } -> ...`) を書くと、
  body で名前が unbound になっていた。現在は通る。
- [`my_destructuring_unbound.yu`](my_destructuring_unbound.yu) —
  `my (a, b) = (1, 2)` / `my { x, ..rest } = rec` / `my [first, ..rest] = xs`
  の destructuring binding が、現在は通る。
- [`list_map_method_unresolved.yu`](list_map_method_unresolved.yu) — list の
  companion method `.map` が解決できなかった。現在は通る。
- [`list_filter_method_missing.yu`](list_filter_method_missing.yu) — list の
  companion method `.filter` が解決できなかった。現在は通る。
- [`list_methods_undocumented_missing.yu`](list_methods_undocumented_missing.yu)
  — docs にある `xs.first` / `xs.rev` / `xs.sort` が stdlib companion method
  として登録されていなかった。現在は通る。
- [`result_methods_undocumented_missing.yu`](result_methods_undocumented_missing.yu)
  — result の `.map` / `.and_then` / `.unwrap_or` が companion method として
  登録されていなかった。現在は通る。
- [`lazy_operator_thunk_in_tuple.yu`](lazy_operator_thunk_in_tuple.yu) —
  lazy infix operator の結果を tuple 要素の位置に置いても、現在は force
  された値が返る。
- [`pattern_binding_vs_variant.yu`](pattern_binding_vs_variant.yu) —
  pattern binding 名が in-scope の variant constructor と一致するときも、
  現在は binding として通る。
- [`labelled_for_var_effect_collision.yu`](labelled_for_var_effect_collision.yu)
  — labelled for + var update で外側 loop の `last 'outer` の effect row が
  壊れていた。現在は通る。
- [`enum_curried_payload_unresolved.yu`](enum_curried_payload_unresolved.yu)
  — 複数 payload variant の `tree::node value left right` 分解が現在は通る。
- [`default_arg_method_recv_unresolved.yu`](default_arg_method_recv_unresolved.yu)
  — default 持ち record pattern の後続引数で receiver type が固まる。
- [`branch_merge_cast_missing.yu`](branch_merge_cast_missing.yu) — 分岐合流
  位置で暗黙 cast boundary が使われる。
- [`list_fold_method_inference_failure.yu`](list_fold_method_inference_failure.yu)
  — `xs.fold 0 (\acc x -> acc + x)` の callback が curried 関数として通る。
- [`record_alias_default_mix.yu`](record_alias_default_mix.yu) —
  「alias + default」と「default only」を混ぜた record pattern も通る。
- [`catch_role_method_thunk_invariant.yu`](catch_role_method_thunk_invariant.yu)
  — role method 経由 effect の catch、handler-in-handler の runtime invariant
  違反が解消された。
- [`string_interp_block_invades.yu`](string_interp_block_invades.yu) —
  `%{...}` 内で `;` や `{` を書いても文字列に侵食しなくなった。
- [`wrap_inside_for_body_leaks_fail.yu`](wrap_inside_for_body_leaks_fail.yu)
  — `for` body 内の `E::wrap` が `fail` を正しく捕まえる。
- [`wrap_does_not_traverse_from_chain.yu`](wrap_does_not_traverse_from_chain.yu)
  — `E::wrap` が `from` 連鎖の narrower error を直接捕まえる。
- [`handler_arm_guard_no_fallthrough.yu`](handler_arm_guard_no_fallthrough.yu)
  — handler arm の `if` guard が偽のとき、次の arm に fall-through する。
- [`error_display_impl_missing.yu`](error_display_impl_missing.yu) —
  `error E:` 宣言から `impl Display E` が自動生成され、`e.show` が通る。
- [`error_display_from_chain_missing.yu`](error_display_from_chain_missing.yu)
  — `error io_err: fs from fs_err` のような from variant を持つ error 宣言でも
  `impl Display io_err` が生成され、from payload の `Display` に委譲する。
- [`handler_recursive_extra_arg_runtime.yu`](handler_recursive_extra_arg_runtime.yu)
  — handler arm 内で `listen(k (), log + o + "\n")` のように handler を
  再帰呼び出ししつつ追加引数を渡すケースが、現在は `((), "hi\n")` を返す。
- [`my_record_spread_rest_inference.yu`](my_record_spread_rest_inference.yu)
  — `my { x, y, ..rest } = expr` の `rest` が record 全体として bind され、
  後段の使用や extra field access も通る。
- [`struct_literal_extra_field_silent.yu`](struct_literal_extra_field_silent.yu)
  — nominal struct constructor の record literal に宣言外 field を書くと
  `unknown record field` として弾く。

## docs に反映済み（2026-05-14）

仕様補足と事実訂正を `web/docs` に書き足した履歴。bug ではないが、初学者の
事故を減らすため docs 側へ追記したもの。

- **enum variant の短い名前は `use enum::*` 必須** — `reference/patterns.md`
  の表行と enum 節に追記。pattern 位置で use なしの `red` が silently に
  fresh binding になる注意も入れた。
- **inline type ascription は `as` を使う** — `reference/types.md` の Type
  variable 節の後に「`as` による inline ascription」節を追加。
- **record の `..rest` は全体を指す** — `reference/patterns.md` の Spread
  節を「`..name` は入力 record 全体を bind する」と書き直し、引き算を提供
  しない理由（型システム上十全には行えない）も添えた。
- **handler は shallow** — `reference/effects.md` の handler 節に
  「Handlers are shallow」サブセクションを追加。`run_console (k "42")` の
  ような自己再帰形で書く理由を明示。
- **`--infer` フラグ → `check` subcommand** — `cheat-sheet.md` /
  `guide/pitfalls.md` / `reference/functions.md` の旧コマンド例を
  `yulang check ...` に統一。
- **install.md の `cargo run` 例に subcommand 追加** — `cargo run -p yulang
  -- run path/to/file.yu` に修正、`check` の使い方も併記。
- **`std::ops::add` → `std::int::add` / `(1).add 2`** —
  `reference/operators.md` の「Calling an operator like a function」節を、
  存在しない path の代わりに role method 経由で書く形に修正。
- **`0..10` は閉区間** — `guide/cheat-sheet.md` と
  `reference/control-flow.md` の `for x in 0..10:` 例に「11 回反復、半開は
  `0..<10`」のコメントを足した。

## 確認方法

```bash
yulang run notes/bugs/<file>.yu
# または
cargo run -q -p yulang -- run notes/bugs/<file>.yu
```
