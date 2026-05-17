# notes/bugs/solved (2026-05-16 切り出し)

`notes/bugs/index.md` で解決済みとなった snippet と、対応する `.yu`
ファイルをここにまとめる。

## 目的

- 親 `index.md` を「**いま壊れている**」ものだけに保つため、解決済みは
  ここに退避する。
- 回帰検出。`yulang run --interpreter` と `yulang run --native` を全
  snippet に流して期待出力と比較し、再発が無いことを定期的に確認できる。
  期待出力は各 snippet 冒頭のコメントに書いてある。
- 過去にどの shape の bug がいつ直ったかの記録。

## 回帰確認

```bash
for f in notes/bugs/solved/*.yu; do
    echo "===== $f ====="
    yulang run --interpreter --print-roots "$f" 2>&1 | tail -5
    yulang run --native --print-roots "$f" 2>&1 | tail -5
done
```

期待出力と食い違いがあったら、その snippet を親 `index.md` の「現在の
未解決」へ戻して、ここから消すか「再発履歴」節を付けるかは状況次第。

## 解決済み一覧（時系列で新しいものが上）

### 2026-05-17 再確認

- [`list.say.md`](list.say.md)
  — `Display::say` default method が list receiver で specialize されず、
  generic `Display::say<'a>` が VM erase まで残っていた件。`[1, 2, 3].say` /
  `["a", "b"].say` / `(each [1, 2, 3] + each [1, 2]).list.say` は VM で通り、
  `say` の改行込み stdout も regression 化済み。
- [`native_handler_self_rewrap_no_accumulate.yu`](native_handler_self_rewrap_no_accumulate.yu)
  — self-recursive shallow handler の再帰 wrap が VM / native とも `("ab", 3)`。
- [`native_undet_once_logic_simple.yu`](native_undet_once_logic_simple.yu)
  — finite `each` の `.list` / `.once` / `.logic` が VM / native とも
  `[1, 2, 3]` / `just 1` / `[1, 2, 3]`。
- [`native_junction_all_short_circuit.yu`](native_junction_all_short_circuit.yu)
  — `all [1, 2, 3] < 5` / `all [1, 2, 3] < 2` / `any [1, 2, 3] > 2` が
  VM / native とも `"all small"` / `"some big"` / `"some big"`。
- [`native_ref_list_mut_lost.yu`](native_ref_list_mut_lost.yu)
  — mutable list ref の index update と `.push` が VM / native とも
  `[1, 2, 3, 4]`。

### 2026-05-16 後半 (round-7 の即時解消分)

- [`native_list_show_returns_close_bracket.yu`](native_list_show_returns_close_bracket.yu)
  — `[1, 2, 3].show` / `.debug` が native で `[1, 2, 3]` / `[a, b]` /
  `["a", "b"]` を返すようになった。`Display` / `Debug` 組み立て経路が
  通った。VM と native で一致。
- [`native_sub_for_return_fall_through.yu`](native_sub_for_return_fall_through.yu)
  — `sub:` 内の `for` body からの `return` が発火するようになり、VM /
  native ともに `999`。`native_sub_for_return_int_value_garbled.yu` と同じ
  shape の regression として round-7 に上がっていたが再修正された。
- [`native_loop_with_returns_bool_lane.yu`](native_loop_with_returns_bool_lane.yu)
  — `loop initial with: our loop state = if cond: state else: loop (...)`
  の戻り値が、`f 5` / `f 4` / `f 3` どれも VM / native ともに `5` を返す。
  `if` branch join 直後の値 lane が bool に潰れる症状が消えた。
- [`native_for_if_var_write_lost.yu`](native_for_if_var_write_lost.yu)
  — `for x in ...:` body 内の `if` で `&var = ...` を書く例が VM / native
  ともに `10` を返す。`if` branch 経由の var write back path が native
  でも繋がった。
- [`native_for_range_console_only_first.yu`](native_for_range_console_only_first.yu)
  — `for x in 0..<3: say x.show` が native でも全 iteration 走り、
  `0 1 2 ()` を出す。range Fold continuation が native の console handler
  frame で閉じる問題が解消した。

### 2026-05-16 (それ以前のセッション)

- [`native_handler_result_display_silent_abort.yu`](native_handler_result_display_silent_abort.yu)
  — 2026-05-16 に native CPS JIT の `ScopeReturn` routing を修正した。
  handler escape continuation が見つかった後の値を `Global` abort にせず、
  `propagate_at_threshold = false` の scoped abort として caller chain を止める。
  自己再帰 shallow handler から返った値に `.show` を当てる例は VM / native
  とも `before show / 99 / after show` を出す。
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

### 2026-05-15 (regression-note のみ、index には載っていなかったもの)

- [`native_effect_handler_tuple_result_prints_pointer.yu`](native_effect_handler_tuple_result_prints_pointer.yu)
  — handler が tuple を返す時に CPS repr が pointer の生値を表示していた。
  VM / native とも `(9, "3\n6\n")`。
- [`native_for_loop_escape_keeps_running.yu`](native_for_loop_escape_keeps_running.yu)
  — outer handler が `return` を捕まえた後も inner fold/for continuation
  が走り、root 値を fallback で上書きしていた。VM / native とも `2`。
- [`native_open_range_for_last_returns_payload.yu`](native_open_range_for_last_returns_payload.yu)
  — open-range `for` + local `last` で native CPS repr が無限ループ。
  VM / native とも `5`。
- [`native_top_level_destructure_binding_recurses.yu`](native_top_level_destructure_binding_recurses.yu)
  — 最上位 destructuring が per-name binding に下がる際 arm body が
  source name を再使用していた。VM / native とも `42`。

### 2026-05-14 (parser / lowering / role / handler 系の解消分)

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
