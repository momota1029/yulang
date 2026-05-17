# notes/bugs index (2026-05-16 round-7 後半 更新)

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

## 現在の未解決（2026-05-17 / 非 native regression）

2026-05-17 時点で現行の非 native regression はなし。

## 現在の未解決（2026-05-15 round-5）

round-5 の非 native snippet は 2026-05-16 時点で全て再現しない。新しい
非 native regression が出たらここへ戻す。

## 現在の未解決（2026-05-15 round-6 / `yulang run --native` との差分）

VM (`yulang run --interpreter`) と native (`yulang run --native`) で結果が
食い違うものを集める。既存の `native_*.yu` snippet と並べる。

### CPS lowering 未対応 / 値違い

- `std::undet` の native CPS 回帰についての古い設計メモ。2026-05-17 時点で
  finite `.once` / `.logic` は再現しないが、bare `branch().list` は下の
  `native_undet_branch_list_returns_scalar.yu` として残っている。
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

- `(each [1, 2, 3]).list` / `.logic` / nested `.once` の
  `branch result type mismatch: expected unit, got std::bytes::bytes` は
  2026-05-16 WIP で runtime lowering 側を修正し、小さい再現
  `my choose x = if true: x else: x; choose ()` は VM regression に追加した。
  open な actual / expected に対して `Cast path -> bytes` を即時 runtime cast
  として選ばない。`JoinEvidence` は semantic value boundary なので、open result
  でも thunk branch arm は force する。残りは render-sink leak ではなく、
  `junction` と `undet` を重ねた native CPS の値違いとして追う。
  2026-05-17 の `RoutedJump` 経路修正で
  `runs_junction_condition_once_through_cps_repr` と
  `runs_junction_condition_without_once_through_cps_repr` は通過する。
  `runs_junction_method_undet_once_through_cps_repr` は CPS eval / repr eval までは
  期待 `:just 18` を返すが、JIT が `:just 3` を返す状態で残っている。
  2026-05-17 の direct return hygiene 修正では、guard stack を持たない
  routed jump だけを同期 thunk force 境界で consume するようにしたため、
  `.once` の value arm 境界は保たれる。
  `std::undet.once` の外側 handler へ戻る `ScopeReturn(prompt=1)` が
  JIT の routed-jump 後に install eval の frame を見つけられず、method 後続の
  continuation が飛ばされている可能性が高い。2026-05-17 追加の trace では
  prompt=1 は最終的に frame-walk で見つかるが、その時点で値がすでに
  `:just 3` になっている。`return_i64` で guarded routed jump を consume する
  実験は `runs_junction_condition_once_through_cps_repr` を `18` に壊したため却下。
  次は outer `.once` の `k true` resumption が `sub::return 3` 以降の
  ordinary continuation (`point { ... }.norm2`) を保持できているかを
  [`native-scary/prompt-8.md`](native-scary/prompt-8.md) の続きで追う。
  追加相談は
  [`render-sink-semantic-type-leak/answer-2.md`](render-sink-semantic-type-leak/answer-2.md)
  /
  [`render-sink-semantic-type-leak/question-3.md`](render-sink-semantic-type-leak/question-3.md)
  に分離した。

## 現在の未解決（2026-05-16 round-7 / 仕様 docs 順守の素朴な書き方からの収集）

`web/docs/reference/` を順に読みながら docs 通りに書いた snippet を
`yulang run --interpreter` と `yulang run --native` で比較し、
食い違いが出たものを 11 件記録した。round-6 の CPS lowering / undet 系より
広い範囲をカバーしている (display, ref, loop, error wrap, junction, for+if 等)。

**2026-05-17 再確認結果**: 11 件中 9 件は再現しない。2026-05-16 後半の
5 件 (list.show / sub:-for return / loop with / for-if var / for-range console) に加え、
self-rewrap handler / finite undet once+logic / junction all / mutable list ref も
VM と native で一致したため `solved/` へ移した。残りは bare `branch().list`
の値破損と `error E:` + `wrap` の native stack overflow。

### 値違い / 値破損

- [`native_undet_branch_list_returns_scalar.yu`](native_undet_branch_list_returns_scalar.yu)
  — 2026-05-17 の部分修正で `(branch()).list` は native でも scalar `0`
  ではなく list に戻った。ただし native の低レベル debug は bool list を
  `[1, 0]` と出す。`(if branch(): 1 else: 2).list` はまだ VM `[1, 2]` /
  native `1` で、`junction` condition continuation から root display へ値が
  漏れる既存 round-6 系の routing bug と見る。

### compile-time reject / runtime crash

- [`native_error_wrap_basic_flow.yu`](native_error_wrap_basic_flow.yu)
  — docs (`reference/errors.md`, `idioms.md`) 推奨の `error E:` + `fail` +
  `E::wrap` flow が、native の 3 経路全部で塞ぐ。今日の build でも
  full 例 (`wrap` 内で `[fs_err]` helper 呼び) は **stack overflow** で
  abort する。
  - `fail E::variant payload`: native CPS 段で
    `CPS lowering does not support free variable 'std::error::Throw::throw' yet`
    で reject。
  - `E::variant payload` (直呼び、`fail` 抜き): native は runtime で boxed
    pointer 風の garbage 値 (`663089232`) を返す。
  - `wrap` 内で `[E]` を持つ helper 経由: native で stack overflow
    (`thread '<unknown>' has overflowed its stack`)。

### 既存 round-6 への補足観察

- round-6 で「`(branch()).list` は `[[1], [0]]`」とあるが、今の build では
  scalar `0` に潰れる (#native_undet_branch_list_returns_scalar 参照)。
- `Ord::lt` / `Eq::eq` が free variable として CPS lowering に届く経路は
  まだあり、native は `"a" < "b"` / `(1, 2) == (1, 2)` を含むファイルを
  そもそも compile できない。VM 側は runtime で blocked になるだけ。
- `native_cps_lowering_unsupported.yu` の guard 最小再現は 2026-05-17 に
  `solved/` へ移した。

## 解決済み

[`solved/index.md`](solved/index.md) に退避した。snippet の `.yu` も
`solved/` フォルダに移動済み。

回帰確認は `solved/index.md` 冒頭の bash one-liner で全 snippet を VM /
native に流して、各ファイル冒頭コメントの期待出力と食い違わないか見る。
再発を見つけたら該当 snippet を本ファイル上の「現在の未解決」へ戻すか、
`solved/index.md` のエントリに「再発履歴」を付ける。

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
