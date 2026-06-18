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
     ただし `marker_frame_*` と request resume がまだ太いため、旧 VM 速度へ近づけるには
     guard / lookup stack を値 wrapper ではなく continuation / closure state へ寄せる次 slice が必要。
2. infer の `drain_analysis` / `resolve_selections` を切る。
   - public examples の static check では `lower.drain` と `lower.resolve` がそれぞれ 100ms 前後。
   - body lowering より analysis/finalize 側に寄っているため、counter を足すならここから。
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
