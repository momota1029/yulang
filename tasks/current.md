# 現在のタスク: yulang — playground 公開後の公開準備

2026-06-17 時点では、新世代 pipeline は playground で主要 smoke が動くところまで来ている。
ここからは、言語機能を無闇に広げるより、公開して触れる状態にするための足場を優先する。

入口と責務は引き続き次を基準に見る。

- `crates/sources` → `crates/infer` → `crates/poly` → `crates/specialize`
- runtime 側: `crates/mono` / `crates/control-vm` / `crates/mono-runtime`
- 共有 UI/LS 側: `crates/yulang-editor` / `crates/yulang-lsp` / `web/playground`
- CLI 入口: `crates/yulang`

作業規約は `/.rules`（= `AGENTS.md`）と `crates/.rules` を見る。
旧実装は仕様ではない。挙動が食い違ったら spec と手計算で正解を確かめる。

## 仕様（実装の根拠）

- `spec/2026-05-31-effect-variable-subtractable.md` — stack 重みによる effect subtraction
- `spec/2026-06-02-role-system.md` — role 制約と discharge
- `spec/2026-06-04-method-selection.md` — ドット選択
- `spec/2026-06-06-invariant-type-sandwich.md` — 不変型と sandwich
- `spec/2026-06-06-syntax-design.md` — 表面構文（parser 実装から抽出）
- `spec/2026-06-07-principal-monomorphization.md`
- `spec/2026-06-14-control-artifact-cache.md` — control artifact cache

spec に無い判断をしたら、コードでなく spec か `notes/design/` に追記する。

## 現在地（2026-06-17）

- playground では list update、nondet once triple、method / property highlighting などの主要 smoke を通した。
- `specialize2` の function candidate 比較は、arg/ret だけでなく arg_effect/ret_effect も見るようになった。
- tuple length / record required field / polyvariant constructor mismatch は direct concrete subtype でも落ちる。
- `std.control.nondet.nondet.#act-method:once` は deep handler 型として export される。
- 直近の確認済み:
  - `cargo fmt --check`
  - `timeout 120s cargo test -q -p specialize -p control-vm -p mono-runtime -- --test-threads=1`
  - `timeout 120s cargo test -q -p yulang -- --test-threads=1`

WSL2 が落ちやすいため、長い test は必ず `timeout` を付ける。

## 直近の優先順位

1. public regression suite を先に固める。
   - playground で見つけた例、effect/thunk/specialize2 の境界、concrete subtype mismatch を小さい fixture にする。
   - 今後の refactor と release 作業の足場になるため最優先。
   - 詳細: `notes/todo/testing.md`
2. `yulang-editor` を LS と playground の共有面に育てる。
   - token classification、diagnostics range、hover/type display を共有する。
   - playground だけ色や型表示がずれる状態をなくす。
   - 詳細: `notes/todo/language-server.md`
3. release / packaging を cargo 前提から外す。
   - 配布 binary、std bundle、cache/bootstrap、playground artifact、Zed/LS binary discovery を決める。
   - 詳細: `notes/todo/release.md`
4. realm/band と compiled-unit cache を pipeline に統合する。
   - source identity、artifact manifest、SCC cache、cross-realm dependency surface を整理する。
   - 詳細: `notes/design/source-realm-band-plan.md`, `notes/todo/static-analysis-speed.md`
5. 高速化は計測を先に置く。
   - phase timing、intern 候補、cache hit/miss、Rowan cost を測ってから触る。
   - 詳細: `notes/todo/static-analysis-speed.md`
6. Yumark は value model から決める。
   - syntax parse 済みの先、AST/IR/type/runtime/playground 表示を設計する。
   - 詳細: `notes/todo/yumark.md`

## 今すぐやる slice

1. control VM の runtime 構造を frame-based continuation へ寄せる。
   - `showcase` では VM eval がまだ 350ms 前後に残り、旧作 bench の
     `(each 1..20 + each 1..20).list.say` 10ms 前後から大きく離れている。
   - 2026-06-18 に `apply_value` / `force_thunk` / primitive apply / continuation wrapper /
     marker frame の分岐別 counter を追加した。
   - `each 1..20 + each 1..20` 系の測定では、表示を外しても `vm_eval` は 160ms 台で、
     主因は root formatting ではない。
   - 現行 runtime は request resume を `Rc<dyn Fn>` chain として持つため、
     request 通過ごとに resume wrapper と marker frame 再導入が積み上がる。
   - 旧作 `archive/crates/yulang-vm/src/vm/control.rs` の `ControlContinuation` /
     `ControlFrame` / `push_frame` / `resume` / `handle_request` を参考に、
     現行 control IR は残したまま runtime の continuation 表現を作り直す。
   - 詳細: `notes/design/control-vm-frame-runtime-plan.md`
   - 2026-06-18 に `Request.resume` / `BindRequest` を削除し、
     runtime continuation を `Continuation { frames: VecDeque<Frame> }` へ移した。
     ordinary eval / bind / catch pass-through / marker resume は frame 化済み。
   - 残りは eval/apply 全体の trampoline 化。
     `std::control::nondet::each(1..3).list` は通常 test stack で通る。
     `all/any` や深い nondet / mutable playground examples は libtest worker の小さい stack で
     まだ溢れうるため、既存の nondet triples と同じく該当 tests は 16MiB stack helper に載せた。
     `cargo test -p yulang -- --test-threads=1` は通るが、runtime 本体として完全に潰すには
     eval/apply 全体を continuation loop へ寄せる次 slice が必要。
   - 旧 VM の direct-known callee に合わせ、top-level lambda / primitive / constructor /
     effect op instance は callee value 化を飛ばして直接 apply するようにした。
     method select も既知 instance なら直接 apply する。
     さらに active guard / add-id stack は同一 marker を重複して積まない。
     これで `showcase` の `instance_eval_calls` は 17k 台から 139、
     `apply_value_calls` は 66k 台から 39k 台へ落ちた。
   - hygiene marker は local / instance read や closure / thunk 作成時に毎回 value wrapper へ
     包むのをやめ、runtime stack の active marker weight として持ち回す形へ寄せた。
     source-level call 境界だけ `apply_scoped_value` で marker を適用し、
     pop / request 境界は既存の close 処理で escaping value / continuation に閉じ込める。
     これで `bench/nondet_20_discard.yu` の `vm_eval` は 198ms 前後、
     `examples/showcase.yu` は 273〜293ms 程度まで落ちた。
     ただし `marker_frame_calls` は showcase で 109784、
     `request_resume_steps` は 133872 あり、まだ太い。
   - request close で積む marker scope は、resume 時に `split_off` / `append` で
     inner frames を並べ替える形から、close 時点で `MarkerEnter` / `MarkerExit` を
     両端へ置く形に変えた。
     runtime の `marker_checkpoints` が active stack の復元位置を持つ。
     これで `bench/nondet_20_discard.yu` の `vm_eval` は 143〜165ms、
     `examples/showcase.yu` は 246〜269ms 程度まで落ちた。
     まだ `MarkerEnter` 自体は continuation frame として残り、
     `request_resume_steps` は showcase で 133872 ある。
   - `MarkerEnter` / `MarkerExit` frame を廃止し、`Continuation` が marker scope metadata を
     持つ形へ移した。scope は「内側に残っている frame 数」を持ち、resume 中に
     `continue_with_current_frame` が frame を追加した場合も同じ scope の内側として数える。
     request が scope を抜ける時は、scope 内に残った frame だけを request continuation へ移してから
     marker を閉じる。
     これで `examples/showcase.yu` の `request_resume_steps` は 133872 から 43681 へ低下し、
     単発測定の `vm_eval` は 196.8ms。`bench/nondet_20_discard.yu` の release / no-cache
     `vm_eval` は 95.4ms。
     次は active guard / add-id scan と marker push/pop 自体を減らすこと。
   - active marker plan は call 境界で `Vec<ValueMarker>` を clone せず、
     `Rc<[ValueMarker]>` として stack から借りて必要な変換だけ行う形にした。
     handler lookup も全 active frame から探すのをやめ、handler を持つ frame だけを
     `active_handler_frames` に分けた。`active_frame_scans` は `examples/showcase.yu` で
     23004 から 11502、`bench/nondet_20_discard.yu` で 18060 から 9030 へ低下。
     repeat 3 の `vm_eval` はそれぞれ 210〜232ms / 103〜109ms で、測定揺れはあるが
     request 時の handler prefix scan は旧 VM の guard stack lookup に近づいた。
   - 次の高速化計画は、外部レビューの見立ても取り込み、次の順で進める。
     1. `vm_eval` を `control_validate` / `runtime_init` / `runtime_execute` /
        `root_format` に分け、旧 VM と同じ execute-only 区間を測る。
     2. multi-shot continuation の deep clone を消す。
        現状は catch で continuation を値化する時と `k(...)` invoke 時に
        `VecDeque<Frame>` を物理 clone している。
        まず clone counter を入れ、次に immutable / persistent snapshot へ寄せる。
     3. `Vec<ValueMarker>` を hot path の基本表現から外す。
        call / resume の marker plan 変換と dedupe を `ScopeId` 風の canonical state に寄せ、
        handler prompt / guard state を continuation snapshot 側へ統合する。
     4. eval / apply / bind / force を一つの machine loop へ寄せ、
        libtest worker stack overflow を runtime 本体側で消す。
     5. `EvalExpr::from_expr`、`CaseArm` / `Pat` / `Block` / `Type` などの static payload を
        ID 化し、frame は動的 state だけを持つ。
        `CapturedEnv` も最終的には dense slot / scope chain へ寄せる。
     この順番では、`nondet::list` 専用 opcode、20x20 専用分岐、list merge native 化は入れない。
   - 2026-06-18 に `run.vm_eval` の内訳として `run.control_validate` /
     `run.runtime_init` / `run.runtime_execute` / `run.root_format` を追加した。
     旧 VM との比較は `runtime_execute` を見る。
   - continuation frame stack を `VecDeque<Frame>` から `VecDeque<Rc<Frame>>` へ移し、
     continuation capture / invoke 時の Frame 本体 deep clone を避けた。
     resume 時に共有 frame を実行する場合だけ `Rc::try_unwrap` 失敗から Frame clone へ落とす。
     `bench/nondet_20_discard.yu` は release / no-cache で `vm_eval` 76.7ms、
     `runtime_execute` 72.4ms。`examples/showcase.yu` は `vm_eval` 161.3ms、
     `runtime_execute` 146.4ms。
     次は `shared_frame_unwrap_clones`、`continuation_marker_scopes_cloned`、
     per-request marker scope close を persistent cursor / canonical scope へ寄せてさらに削る。
   - continuation marker scopes も `Rc<[ContinuationMarkerScope]>` として shallow clone にし、
     resume 時の active marker plan は既存の `Rc<[ValueMarker]>` をそのまま
     `active_marker_plans` へ積むようにした。
     これで continuation resume ごとの `markers.to_vec() -> Rc<[ValueMarker]>` 再確保を避ける。
     repeat 3 の `runtime_execute` は `bench/nondet_20_discard.yu` で
     54.5ms / 58.2ms / 58.1ms、`examples/showcase.yu` で
     119.4ms / 133.4ms / 129.6ms。
     zero payload frame を inline enum にする案は `shared_frame_unwrap_clones` を減らしたが
     実時間が悪化したため採用しない。
   - static payload ID 化の前段として、case arms を `ExprId` 単位で
     `Rc<[CaseArm]>` cache に載せた。`Frame::Case*` と `BindThen::CaseArm` は
     `Vec<CaseArm>` ではなく共有 slice を持つ。
     `EvalExpr::from_expr` も case arms 本体を clone せず、scrutinee だけを持つ。
     repeat 3 の `runtime_execute` は `bench/nondet_20_discard.yu` で
     53.0ms / 59.0ms / 57.8ms、`examples/showcase.yu` で
     127.4ms / 119.2ms / 119.4ms。
   - 2026-06-19 時点の外部レビュー整理は
     `notes/design/2026-06-19-control-vm-bottleneck-review.md`。
     次の本命は、`Value` / `Thunk` / `Closure` / `FunctionAdapter` の cheap-clone handle 化と、
     `CapturedEnv` の HashMap COW を避ける parent/scope-chain 化。
     先に `env_cow_clones` / `env_cow_entries_copied` / `value_clones_by_variant` /
     `frame_allocs` / `marker_scope_frame_touches` を測り、効く順に切る。
     その後、inline current frame stack + captured snapshot 分離、ScopeId 風 marker state、
     dense env と組み合わせた `PatPlanId` 化へ進む。
   - `CapturedEnv` は 2026-06-19 に one-binding persistent frame chain へ変更した。
     `Rc<HashMap>` COW は消え、`bench/nondet_20_discard.yu` は repeat 5 で
     `runtime_execute` 45ms 前後まで落ちた。
     `im_rc::HashMap<_, _, FxBuildHasher>` 版も測ったが、同条件で
     `bench/nondet_20_discard.yu` が 52〜55ms、`examples/showcase.yu` が 115〜125ms となり、
     親ポインタ版より悪化したため採用しない。
     現状は `env_max_size=5` なので、HashMap の O(1) lookup より浅い frame chain が勝つ。
   - `Value` のうち control payload が大きい `Closure` / `RecursiveClosure` /
     `Thunk` / `FunctionAdapter` は `Rc` handle 化した。
     `bench/nondet_20_discard.yu` は repeat 5 で `runtime_execute` 42〜45ms、
     `examples/showcase.yu` は 92〜98ms 台まで下がった。
     次の本命は、まだ `frame_allocs` と `marker_scope_frame_touches` が大きいため、
     通常実行 stack と captured snapshot を分けること、または marker scope touch を
     pointer state 化すること。
     active marker scope の `frames_remaining` を `frame_delta` cursor へ寄せる案は試したが、
     `runtime_execute` が改善せず、複雑性に見合わないため採用しない。
     `FrameSlot::{Owned, Shared}` で通常 frame allocation を消す案も試したが、
     `frame_allocs` は落ちても `runtime_execute` が悪化したため採用しない。
     frame stack を触るなら先に frame payload をさらに小さくする。
     `SharedMarkers` の continuation resume 変換には identity fast path を入れ、
     `examples/showcase.yu` は repeat 5 で 90〜96ms へ下がった。
     structural values (`Tuple` / `Record` / variant payload) も `Rc<[...]>` 化し、
     `examples/showcase.yu` は repeat 5 で 86〜94ms まで下がった。
     `Value::Marked` / `Frame::MarkValue` の marker payload も `Rc<[ValueMarker]>` 化し、
     escaping marked value / frame clone で marker list を複製しないようにした。
     `examples/showcase.yu` は repeat 5 で 83〜89ms へ下がった。
     空の continuation marker scopes は `Option<Rc<[ContinuationMarkerScope]>>` の `None`
     で表し、`Continuation::default()` で空 `Rc` を作らないようにした。
     `examples/showcase.yu` は repeat 5 で 82〜88ms へ下がった。
     record/list pattern bind が保持する marker payload も `Rc<[ValueMarker]>` 化し、
     `examples/showcase.yu` は repeat 5 で 80〜84ms まで下がった。
     marked callee apply の call/resume marker 変換も shared fast path に載せ、
     `examples/showcase.yu` は repeat 5 で 73〜79ms まで下がった。
     pattern bind sequence は reversed stack + `pop()` に変え、
     `examples/showcase.yu` は repeat 5 で 73〜76ms に寄った。
     request が innermost marker scope を抜ける時の outer scope 全更新は、
     resume 中の `request_close_offset` で遅延適用するようにした。
     `marker_scope_frame_touches` は `bench/nondet_20_discard.yu` で 1287567 から 571487、
     `examples/showcase.yu` で 1024079 から 452587 へ下がり、
     request-close 分の touch は 0 になった。
     `SharedMarkers` を持つ value wrapping は `Rc<[ValueMarker]>` をそのまま
     `Value::Marked` へ共有する fast path に寄せ、function adapter hygiene も生成直後に
     shared marker frame へ載せた。
     `examples/showcase.yu` は repeat 5 で 68〜71ms まで下がった。
     さらに、すでに marked な value が新 marker を含んでいる場合は merge / dedupe を飛ばす
     fast path を入れた。
     `examples/showcase.yu` は repeat 5 で 66〜71ms まで下がった。
     record pattern の reversed stack 化と `CapturedEnv` の unique multi-binding frame 化は
     悪化したため採用しない。
     `AddIdMarker` から未使用の `path: Vec<String>` を外し、runtime hot path では
     `InternedPath` だけを持ち回るようにした。
     `bench/nondet_20_discard.yu` は repeat 5 で 24〜25ms、
     `examples/showcase.yu` は repeat 5 で 49〜54ms まで下がった。
     marker / handler 側の path key も full `InternedPath` ではなく copy な
     `InternedPathPrefix { id, len }` にし、request / operation 側だけ full key を保つようにした。
     `bench/nondet_20_discard.yu` は repeat 5 で 22〜23ms、
     `examples/showcase.yu` は repeat 5 で 45〜47ms まで下がった。
     resume 中の `continue_with_current_frame` value path は、frame を continuation に積み直さず
     その場で `apply_frame` するようにした。
     `examples/showcase.yu` は repeat 5 で 41〜44ms まで下がった。
     `active_marker_plans` に function-call marker を cache する案は悪化したため採用しない。
     playground deploy 後に全 run が `unreachable` になった原因は、`control-vm` の timing が
     wasm32-unknown-unknown で未実装の `std::time::Instant` を直接使っていたこと。
     `control-vm::runtime::time` shim で wasm では zero-duration timing にし、
     `wasm_bg-FqFJxbJK.wasm` を build / deploy 済み。
2. infer の `drain_analysis` / `resolve_selections` を切る。
   - public examples の static check では `lower.drain` と `lower.resolve` がそれぞれ 100ms 前後。
   - body lowering より analysis/finalize 側に寄っているため、counter を足すならここから。
   - 2026-06-19 に SCC graph 自体の self-time を `analysis.scc_apply` として分離し、
     reachability / merge / rebuild / payload sort / pending use scan / ready check の counter を追加した。
     `DependencyAdded` は instantiation payload を作らず、component adjacency だけを張るようにした。
     `examples/showcase.yu` の release / infer timing では
     `analysis.route_scc_events=162.1ms` に対して `analysis.scc_apply=895us`。
     SCC graph そのものより、`analysis.quantify_generalize=90.6ms`、
     `analysis.instantiate_subtype_predicate=42.6ms`、`constraint.drain=85.2ms` が本命。
   - 続けて generalize compact shape counter を追加し、
     `examples/showcase.yu` では `generalize_root_compact_vars=5627` と
     `generalize_component_unique_compact_vars=5627` が一致した。
     この入力では component 内 root overlap は薄く、
     `generalize_compact_iteration_nodes=26244` が `generalize_root_compact_nodes=15871` まで
     膨らむ restart 側が濃い。
     次は merge/subtype/role restart をどう減らすか、または restart 後の compact / role view を
     constraint epoch で再利用できるかを見る。
   - var-only interval merge を小さい場合も direct var-var path にする案は、
     `generalize_merge_restarts` を減らしたが role prepass の正しさを壊したため採用しない。
     採用した軽量化は、bound replay snapshot の `SmallVec` 化、
     role 入力なし def での applied role set clone 回避、
     finalize 用 `def_parent_map` の def 数 cache。
     compact shape counter は `YULANG_GENERALIZE_SHAPE_TIMING=1` の時だけ tree walk する。
     `examples/showcase.yu` の release / infer-only repeat 5 では `infer` が概ね `230〜238ms`。
3. source/load は今の public examples では最大ではない。
   - `collect+load` は 70〜85ms 程度なので、realm/band や compiled-unit cache と合わせて設計する。
   - 先に std 専用特例で隠さない。

## 守る不変条件

- 型が決まらないから Top 相当へ逃がす処理は入れない。
- path / module / fixture 名の文字列比較で型を決めない。
- 再現ケースだけを通す局所分岐ではなく、一般規則として説明できる修正にする。
- infer に不動点計算のような重たい反復を足さない。まず一回の線形パスで設計する。
- テスト期待値を実装出力に合わせて書き換えない。
- effect row subtraction の shallow/deep handler 境界を後段の整形で潰さない。

## 外側の予定

- 相談先の先生への研究相談（effect row subtraction の切り出し）は、
  **実装完了＋公開用 regression が揃ってから**送る。素材は `notes/effect-inference-overview.md`。
- 2026 年 7 月以降は忙しくなる予定。12 月のアドベントカレンダーが公開目標。

## 旧 roadmap

2026-05-25 起点の post-native roadmap（monomorphize / runtime type surface、
static analysis speed、parser combinators、host IO、native backend の退役整理）は
`tasks/done/2026-05-25-post-native-roadmap.md` へ退避した。
そこに残る TODO は、archive の参照が必要なときだけ現行 crate へ拾い直す。
