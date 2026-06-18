# control VM frame runtime plan

現行の `crates/control-vm` は `mono::Program` から軽い control IR を作るところまでは
今の公開 pipeline に合っている。一方で runtime は、effect request を受け流すたびに
`Rc<dyn Fn>` resume closure を重ねる形になっており、nondet / handler heavy なコードで
旧作 control VM よりかなり遅い。

このメモは旧作 `archive/crates/yulang-vm/src/vm/control.rs` の構造を参照しつつ、
現行 IR を捨てずに runtime だけを frame-based continuation へ寄せる計画を固定する。

## 現在の観測

2026-06-18 時点の `showcase` は、`Expr` clone 削除、COW env、scalar marker fast path、
value continuation fast path を入れたあとでも `vm_eval` が 350ms 前後に残る。

旧作でよく使っていた形に近いベンチ:

```yu
use std::control::nondet::*
{ my xs = (each 1..20 + each 1..20).list; () }
```

では release build / no-cache で `vm_eval` が 160ms 台だった。`.say` や root formatting を
外しても大きく変わらないので、主因は表示ではない。

同じ実行で目立つ counter は次の通り。

- `effect_requests`: 約 860。
- `request_resume_steps`: 約 35k。
- `marker_frame_calls`: 約 67k。
- `marker_frame_request_closes`: 約 32k。
- `marker_frame_resume_steps`: 約 50k。
- `path_prefix_checks`: 約 74k。
- `active_add_id_scans`: 約 65k。

10x10 に縮めると `vm_eval` は 30ms 前後まで下がるが、request あたりの marker / resume
再導入がまだ多い。したがって arithmetic や list merge より、
effect request の通過と continuation resume の表現が太い。

## 現行 runtime のボトルネック

現行 runtime は `EvalResult::Request(Request { resume: Rc<dyn Fn(...)>, ... })` を持つ。
`continue_with_request` / `continue_bind_request` / `continue_bind_result` /
`continue_value_as_bind` は request が出るたびに `request.resume` をもう一枚 wrap する。

この形では、source 上の「あとで続ける」が request 発生時点で heap closure chain になる。
さらに `MarkerFrame` は request が frame を抜けるたびに resume closure を作り直し、
resume 時に同じ marker plan を再導入する。nondet `.list` のように continuation を
何度も呼ぶコードでは、同じ wrapper chain を何度も通る。

path interning は入っているが、dispatch はまだ active frame / active add id scan と
prefix match が中心で、request 数に対して frame 数が掛かる。

## 旧作 control VM から採る構造

旧作は request resume を closure ではなく、データとしての continuation で持つ。

参照する入口:

- `archive/crates/yulang-vm/src/vm/control.rs`
  - `ControlContinuation`
  - `ControlFrame`
  - `push_frame`
  - `resume`
  - `apply_frame`
  - `handle_request`
  - `split_handle_continuations_owned`
  - `push_thunk_boundary_frame`
- `archive/crates/yulang-vm/src/vm/model.rs`
  - `VmContinuation`
  - `Frame`
  - `GuardStack`
  - `BlockedEffect`
- `archive/crates/yulang-vm/src/vm/continuation.rs`
  - `inside_handle`
  - `outside_handle`

旧作の中心は次の形。

```rust
struct ControlContinuation {
    frames: VecDeque<ControlFrame>,
    guard_stack: GuardStack,
    lookup_stack: GuardStack,
}

fn push_frame(mut request: ControlRequest, frame: ControlFrame) -> ControlRequest {
    request.continuation.frames.push_front(frame);
    request
}

fn resume(&mut self, mut continuation: ControlContinuation, mut value: ControlValue) {
    while let Some(frame) = continuation.frames.pop_back() {
        value = self.apply_frame(frame, &mut continuation, value)?;
    }
}
```

request が途中で出たら、その request の continuation に frame を push するだけでよい。
resume closure をその場で作り直さない。handler は request continuation を split して、
handler 内側の continuation を resume value として渡す。

## 採らないもの

旧作を仕様として復活させない。次は移植しない。

- 旧 typed IR / runtime IR への依存。
- finalized-to-legacy projection の補修。
- effect payload thunk を後段で雑に force する修正。
- std nondet だけを速くする path / fixture 特例。
- inference / lowering 側の意味変更。

現行 `crates/control-vm/src/ir.rs` は維持し、`mono::Program -> control-vm::ir::Program`
の lowerer も維持する。変える中心は runtime の continuation/request 表現。

## 新 runtime の目標形

最初の実装目標は、現行 runtime と同じ `Value` / `Expr` / `Pat` を読みながら、
`Rc<dyn Fn>` resume chain をなくすこと。

```rust
struct FrameContinuation {
    frames: Vec<Frame>,
    marker_state: MarkerState,
}

struct FrameRequest {
    operation: EffectOpId,
    payload: Value,
    continuation: FrameContinuation,
    blocked: SmallGuardSet,
}

enum Frame {
    ForceValueIfThunk,
    AdaptValue { source: Type, target: Type },
    ApplyCallee { arg: ExprId, env: CapturedEnv },
    ApplyArg { callee: Value },
    BindPat { pat: Pat, env: CapturedEnv, next: BindNext },
    Case { scrutinee: Value, arms: Vec<CaseArm>, env: CapturedEnv, index: usize },
    Catch { arms: Vec<CatchArm>, env: CapturedEnv },
    CatchValue { arms: Vec<CatchArm>, env: CapturedEnv, index: usize },
    CatchRequest { arms: Vec<CatchArm>, env: CapturedEnv, index: usize },
    MarkerFrame { state: MarkerState },
    BlockStep { stmts: Vec<Stmt>, tail: Option<ExprId>, env: CapturedEnv, index: usize },
}
```

この sketch はそのまま確定 API ではない。大事なのは、
「request の外側へ continuation を伝える操作」が closure wrap ではなく
`Frame` push になること。

## effect / marker の扱い

現行の `Value::Marked` は、marker frame から出た value があとで effect request を発火する時に
handler hygiene を保つためにある。ただし scalar value には不要で、すでに fast path を入れた。

frame runtime では、最終的に次を目指す。

- effect operation は `Vec<String>` 比較ではなく、lowering 時に intern した `EffectOpId` で扱う。
- handler frame は active scan ではなく continuation / prompt stack 上の frame として持つ。
- function adapter hygiene は `Value::Marked` の広い marker propagation ではなく、
  adapter call / resume に必要な guard state snapshot として持つ。
- request が handler を抜けるとき、旧作の `BlockedEffects` frame 相当で guard を request に付ける。

この段階までは意味論に触れやすいので、まず `Rc<dyn Fn>` を frame 化してから着手する。

## 移行手順

### 1. 現行 runtime のまま、frame continuation の型を導入する

`runtime/continuation.rs` を作り、`FrameContinuation` / `Frame` / `FrameRequest` の
最小型を置く。最初は既存 runtime と併存させ、public API は変えない。

この段階で benchmark と parity test を固定する。

- `showcase`
- `(each 1..10 + each 1..10).list`
- `(each 1..20 + each 1..20).list`
- ref update inside list
- function adapter + `sub::return`
- nested catch / resume

### 2. ordinary eval continuation を frame 化する

`continue_with` のうち、request でない value path は今のままでもよい。
request path は `Request.resume = Rc<dyn Fn>` ではなく、request continuation に
対応 frame を push する形へ移す。

最初に対象にする frame:

- `ApplyCallee`
- `ApplyArg`
- `ForceThunkValue`
- `AdaptValue`
- `Coerce`
- `TupleItem`
- `RecordField`
- `BlockStep`

ここでは handler split にはまだ触らず、既存 `Catch` の外側 pass-through に相当する
frame だけを作る。

### 3. pattern bind continuation を frame 化する

`bind_pat_sequence` / `bind_record_pat` は現在 `Rc` closure と `Vec::remove(0)` /
`clone()` の再帰になっている。ここを `BindFrame` で持つ。

これは `.list` の主因ではなさそうだが、handler guard / pattern arm が増えると効く。
request 途中復帰の契約を ordinary eval と揃える意味もある。

### 4. catch / handler を frame continuation の本線へ移す

現行 `handle_catch_request_arm` は、対象外 request の resume を
`handle_catch_result(resumed, arms, env)` で包む。これが `request_resume_steps` を増やす。

frame runtime では `Catch { arms, env }` frame を request continuation に残し、
外側へ投げる request はその frame を保持する。matching handler では
旧作の `split_handle_continuations_owned` 相当で outer / inner を分ける。

continuation value は `FrameContinuation` snapshot を持つ multi-shot value にする。
resume は snapshot を clone して frame loop に戻す。

### 5. marker / guard stack を prompt frame 化する

`active_frames` / `active_add_ids` / `active_marker_plans` の global stack scan を減らす。
handler / marker / add-id は continuation frame 側に寄せる。

この段階で `path_prefix_checks` と `active_add_id_scans` が落ちるかを見る。

### 6. direct call / primitive fast paths を戻す

旧作には `direct_known_callee` と `eval_direct_binary_primitive` があった。
frame runtime で semantics が安定したあと、現行 IR でも同じ狙いを入れる。

これは最初にやらない。今の主因は primitive 自体ではなく continuation / marker なので、
先に構造を変える。

## 完了条件

最初の節目は次の状態。

- `control-vm` parity tests が通る。
- `yulang --runtime-phase-timings run` の public examples が現行と同じ stdout / root value を返す。
- 20x20 nondet list discard が release build で現行より明確に速い。
- `request_resume_steps` 相当の closure wrapper counter が消える、または frame step counter として説明できる。
- `showcase` の `vm_eval` が 350ms 付近から大きく下がる。

10ms に戻るには、frame runtime だけでなく direct call / primitive / handler dispatch の
追加最適化も必要かもしれない。ただし、closure chain のままではそこまで届かない。
