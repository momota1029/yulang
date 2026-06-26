## 推奨設計: **immutable continuation snapshot + resume cursor + segmented frame view**

これを本命にするのがよさそうだねぇ。

今のボトルネックは、`Frame` 自体の deep clone というより、`Continuation { frames: VecDeque<SharedFrame>, marker_scopes: ... }` の `#[derive(Clone)]` が、capture / invoke ごとに frame handle 列をなぞるところだよ〜。現状 `Continuation` は `VecDeque<SharedFrame>` を直に持っていて、clone path は `clone_continuation_for_capture` で `continuation.clone()`、invoke 側も `Runtime.continuations` から `.clone()` してから resume に渡している。

ただし、**`Rc<[SharedFrame]> + range/cursor` を `VecDeque` の単純な置換にするのは危ない**。理由は `push_front` / `prepend_frames` / `split_back_frames` が今の continuation 構築・request 再発行に深く絡んでいるからだねぇ。`resume` は `pop_back()` で進むし、request が marker scope を外へ出る時は back 側を split して request continuation に prepend している。

なので形としてはこう。

```rust
// 概念図
struct StoredContinuation {
    frames: FrameSnapshot,
    marker_scopes: Option<SharedMarkerScopes>,
}

#[derive(Clone)]
struct FrameSnapshot {
    segments: Rc<[FrameSegment]>, // まずは SmallVec でも可
}

#[derive(Clone)]
struct FrameSegment {
    frames: Rc<[SharedFrame]>,
    start: usize,
    end: usize,
}

struct ResumeContinuation {
    frames: FrameCursor,          // mutable cursor
    marker_scopes: Option<SharedMarkerScopes>,
    consumed_frames: usize,
}

struct FrameCursor {
    segments: SmallVec<[FrameSegment; 2]>,
    // pop_back は cursor だけ動かす
}
```

ポイントは、**snapshot は絶対に pop しない**こと。`resume` 中に動くのは `ResumeContinuation` の cursor だけ。multi-shot continuation を何度 invoke しても、毎回 cursor を作るだけで、snapshot の frame handle 列は共有する。

さらに、request が snapshot resume 中にまた request を出す場合があるから、`Rc<[SharedFrame]>` 1枚だけだと足りないことがある。`split_back(count)` で suffix view を作り、`prepend_frames` は segment list をつなぐだけにしたい。ここで flatten すると、結局 `VecDeque clone` の別名になるよ〜。

---

## 5つの相談への答え

### 1. `Rc<[SharedFrame]> + range/cursor` は妥当か

**妥当。ただし “flat slice 1枚” ではなく、segment view にしておくのが安全。**

最低ラインはこれ。

```rust
enum ContinuationFrames {
    Owned(VecDeque<SharedFrame>),      // request を組み立て中、one-shot 用
    Snapshot(FrameSnapshot),           // stored multi-shot 用
    Segmented(FrameSegments),          // snapshot suffix + 新しい prefix
}
```

`Owned(VecDeque)` は、未共有の request continuation を作る時だけ残していい。`push_frame` は今 `push_front(shared_frame(...))` なので、ここを全部 immutable slice にすると、1 frame 追加ごとに配列を作り直す罠がある。

大事なのは、**capture / invoke で frame handle 列を clone しないこと**。`continuation_capture_clones` と `continuation_invoke_clones` はイベント数として残ってもいいけど、`continuation_frames_cloned` は「実際に copied handles を数える counter」に変えるなら大きく落ちるはず。

### 2. resume 中に `pop_back` する命令列と captured snapshot は分けるべきか

**分けるべき。ここはかなり強めにそう思う。**

今は `resume(&mut self, mut continuation: Continuation, ...)` が continuation 本体を消費して、`frames.pop_back()` で進む。

multi-shot では、stored continuation は値として再利用される。だから stored 側を cursor で直接動かす設計は、`RefCell` などで隠しても意味論的にアウト寄りだねぇ。
正しくは、

```text
StoredContinuation  --invoke-->  ResumeContinuation(cursor)
```

という一方向の変換にする。

この形なら、invoke は `Rc` clone + cursor 初期化だけになる。`Runtime.continuations.get(...).clone()` で `VecDeque` を丸ごとなぞる今の path を消せる。

### 3. multi-shot / one-shot continuation を runtime で分けられるか

**分けられる。ただし user-visible continuation を勝手に one-shot 扱いするのはダメ。**

安全な線引きはこうだねぇ。

| 種類                                                                         | 扱い                     |
| -------------------------------------------------------------------------- | ---------------------- |
| request が host まで出て、そのまま `resolve_host_requests` で resume される continuation | one-shot owned のままでよい  |
| handler が continuation 変数を bind せず、その request を処理するだけ                      | one-shot に近い           |
| `Value::Continuation(id)` としてプログラムに渡る continuation                         | multi-shot 固定          |
| `Runtime.continuations` に格納された continuation                                | multi-shot snapshot 固定 |

現状も `Value::Continuation(id)` は thunk に入り、force 時に `Runtime.continuations` から取り出して clone している。ここが multi-shot の境界として自然だよ〜。

`Rc::strong_count == 1` だから one-shot、みたいな shortcut は避けた方がいい。値として同じ continuation を2回使う意味論があるなら、参照カウントの都合で挙動を変えるのは危ない。

### 4. `marker_scopes` と active marker frame push/pop はどう結びつけるべきか

**`marker_scopes` は snapshot の一部、active marker frame は resume run の一時状態、と分けるのがいい。**

今の `ContinuationMarkerScope` は `frames_remaining` を持っていて、request continuation の frame 数に対する boundary として記録されている。`close_marker_request` は `request.continuation.frames.len()` を読んで scope を prepend している。

snapshot 化後は、`frames_remaining` をそのまま使うより、

```rust
close_after_pops: usize
// または
close_at_cursor: LogicalFramePos
```

みたいな **cursor 座標** に寄せた方が安全だと思う。`split_back_frames` が view になるから、`len()` に依存した境界管理を続けると off-by-one が出やすい。

active marker frame は今の通り、resume 開始時や scope enter 時に runtime stack へ push し、checkpoint で pop するのが安全。`active_frames`, `active_handler_frames`, `active_add_ids`, `active_marker_plans` は request marking の順序に関わるから、snapshot 内にキャッシュしない方がいい。実際、request marking は active add-id marker を順に見て guard を付けている。

ただ、次の段階では `marker_scope_frame_touches` を減らす余地がある。進捗メモでも、marker scope touch は `consume_marker_frame` 側が本筋だと書かれている。

方向性は、scope ごとに毎 frame 消費を伝播するのではなく、**次に閉じる boundary だけを見る event/cursor 型**にすること。

```text
resume cursor が進む
→ consumed_frames += 1
→ next_scope.close_after_pops == consumed_frames なら close
→ それ以外は何もしない
```

これなら `marker_scope_consume_touches` / `marker_scope_frame_touches` は、理想的には `request_resume_steps` 比例から `marker_scope_close_pops + marker_scope_request_closes` 近辺へ寄る。

### 5. semantic risk が高い shortcut

避けたいのはこのへん。

| shortcut                                                     | 何が危ないか                                                                                              |
| ------------------------------------------------------------ | --------------------------------------------------------------------------------------------------- |
| captured snapshot の cursor を直接 mutate                        | multi-shot continuation の2回目以降が壊れる                                                                  |
| `Rc<[SharedFrame]>` へ毎回 flatten                              | counter 名だけ変わって、実体は handle 列コピーのまま                                                                  |
| `push_front` のたびに slice 作り直し                                 | capture clone より悪い局所コストになる                                                                          |
| active marker / add-id marker を path や id で sort/dedup       | request marking の順序・handler hygiene が壊れうる                                                           |
| `active_frames` / `active_add_ids` を snapshot にキャッシュ         | entry frame length と handler boundary が runtime stack 依存なので危険                                       |
| `Rc::strong_count` で user-visible continuation を one-shot 判定 | multi-shot 意味論と衝突する                                                                                 |
| ScopeState indexed query の再投入                                | 以前、`active_add_scans` は減っても `runtime_execute` が悪化している。HashMap 更新・sort/dedup・foreign-only merge が重い。 |
| path/name 特別扱い                                               | 今回の制約にも反するし、nondet 以外で壊れやすい                                                                         |

---

## 案の比較

| 案                                                                    | 内容                                                                                                         |                                                            意味論リスク | 実装量 | 減る counter / 減らない counter                                                                                                                                                                                    |
| -------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------: | --: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **A. 推奨: immutable snapshot + resume cursor + segmented frame view** | stored continuation は immutable snapshot。invoke は cursor を作るだけ。request 中の split/prepend は segment view で表現 | 中。frame 順序、`split_back`, marker close boundary の off-by-one が主リスク | 中〜高 | **減る:** `continuation_frames_cloned` の実コピー、`continuation_invoke_clones` に伴う handle列コピー、`continuation_marker_scopes_cloned` の実コピー。**減らない:** `request_resume_steps`, `marker_frame_pushes`, `active_add_scans` |
| B. persistent deque / rope を continuation 全体に導入                      | `VecDeque` をやめて、push_front / pop_back / split / prepend が O(log n) or O(segments) の永続構造へ                   |                      中〜高。構造が複雑で resume hot path に overhead が乗りやすい |   高 | **減る:** capture/invoke の frame handle列コピー、`prepend_frames` のコピー。**悪化しうる:** `request_resume_steps` あたりの per-step cost                                                                                         |
| C. one-shot / multi-shot specialization                              | unescaped request continuation は owned のまま、first-class continuation だけ snapshot 化                          |                 中。user-visible continuation を誤って one-shot にすると壊れる |   中 | **減る:** host/internal one-shot path の `continuation_frames_cloned`, 場合により `shared_frame_unwrap_clones`。**100x nondet では限定的:** stored multi-shot が多いなら `continuation_invoke_clones` 本体には効きにくい                 |

私なら **A を先に入れる**。B はきれいだけど、resume hot path にデータ構造コストを持ち込むのが怖い。C は安全にやる価値はあるけど、今回の 100x nondet の主犯っぽい `continuation_frames_cloned: 6,360,700` / `continuation_marker_scopes_cloned: 7,988,400` に正面から刺さる感じは A の方が強い。

---

## counter ベースの期待値

今の 100x workload で見るなら、期待はこう。

| counter                                      | 推奨案Aでの期待                                                                                                                             |
| -------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ |
| `continuation_capture_clones: 86100`         | **イベント数としては残る**。ただし “clone” ではなく “snapshot capture/share” に変える                                                                       |
| `continuation_invoke_clones: 84000`          | **イベント数としては残る**。ただし frame handle列 clone は消える                                                                                         |
| `continuation_frames_cloned: 6360700`        | **主ターゲット**。actual copied handles counter にするなら大きく下がる。理想は snapshot materialize 時だけ                                                    |
| `continuation_marker_scopes_cloned: 7988400` | 現状 `marker_scopes` は persistent cons list 化済みなので、これは「実コピー」より「logical shape count」寄り。actual copied scope nodes counter に変えるならほぼ消せるはず。 |
| `request_resume_steps: 1518200`              | 減らない。これは実際に VM frame を進める回数                                                                                                          |
| `marker_frame_pushes: 6186900`               | snapshot 化だけでは減らない。resume marker を active stack に積む意味論が残る                                                                            |
| `active_add_scans: 3263400`                  | snapshot 化だけでは減らない。ScopeState frontier か active marker query の別問題                                                                    |
| `marker_scope_frame_touches` 系               | A の後、marker boundary を cursor/event 化すると減らせる。A単体では無理に触らない方が安全                                                                        |

ここで大事なのは、古い `continuation_frames_cloned` をそのまま「shape counter」として残すと、実装が速くなっても数字が減らないこと。
`*_cloned` は actual copy counter にし、shape は `continuation_snapshot_frames_observed` みたいに分けるのがいいよ〜。

---

## Codex に投げる実装タスク 3段階

### 1段階目: frame storage abstraction と counter 整理

**目的:** 意味論を変えずに、`VecDeque<SharedFrame>` 直触りを隠す。

Codex へのタスク文:

```text
crates/control-vm/src/runtime/frame.rs の Continuation.frames を直接 VecDeque として操作している箇所を抽象化する。

やること:
- ContinuationFrames 型を追加する。
- 初期実装は内部で VecDeque<SharedFrame> を持つだけでよい。
- 以下の操作を method 化する:
  - len
  - is_empty
  - push_front
  - pop_back
  - back
  - split_back(count)
  - prepend_to(other)
  - take_all
- push_frame, push_continuation_frame, split_back_frames, prepend_frames, resume loop, finish_inline_request, finish_resume_request をこの API 経由に置き換える。
- RuntimeStats の continuation_frames_cloned / continuation_marker_scopes_cloned を、actual copied handles/nodes と logical shape observation に分ける。
- この段階では性能改善を狙わず、cargo test -p control-vm と既存 nondet benchmark の counter がほぼ変わらないことを確認する。
```

この段階の成功条件:

```text
request_resume_steps: 同じ
marker_frame_pushes: 同じ
active_add_scans: 同じ
continuation_frames_cloned: 旧定義なら同じ、new actual-copy counter は旧値と一致
```

### 2段階目: stored multi-shot continuation を snapshot + cursor 化

**目的:** capture / invoke の `VecDeque<SharedFrame>` handle列 clone を消す。

Codex へのタスク文:

```text
Runtime.continuations に格納する continuation を StoredContinuation snapshot に変更する。

やること:
- StoredContinuation { frames: FrameSnapshot, marker_scopes } を追加する。
- ResumeContinuation { frames: FrameCursor, marker_scopes, consumed_frames } を追加する。
- Runtime::store_continuation は ContinuationFrames を immutable snapshot として共有する。
- force_thunk の Thunk::Continuation path では StoredContinuation を clone せず、ResumeContinuation cursor を作る。
- clone_continuation_for_capture / clone_continuation_for_invoke は、frame handle列 clone ではなく snapshot share / cursor creation の stats を記録する。
- FrameSnapshot は最初は Rc<[SharedFrame]> + range でよいが、request during resume で flatten しないよう FrameSegment / SmallVec segment に対応する。
- finish_resume_request と close_innermost_marker_request の split/prepend は segment view を移動するだけにする。
- snapshot は immutable とし、resume 中に snapshot 側の cursor を変えない。
```

この段階の期待 counter:

```text
continuation_capture_clones: イベント数としてはほぼ同じ
continuation_invoke_clones: イベント数としてはほぼ同じ
continuation_frames_cloned: actual copied handles として大幅減
continuation_marker_scopes_cloned: actual copied nodes としてほぼゼロ寄り
request_resume_steps: 同じ
marker_frame_pushes: 同じ
active_add_scans: 同じ
```

注意点:

```text
Rc::try_unwrap に頼る owned-frame fast path は snapshot resume では基本的に期待しない。
snapshot resume では borrowed apply path を使い、borrowed にできない Frame だけ clone_shared_frame に落とす。
one-shot request continuation は Owned(VecDeque) のまま残し、既存の Rc::try_unwrap fast path を殺さない。
```

### 3段階目: marker scope boundary を cursor/event 化

**目的:** snapshot 化とは別に、`marker_scope_frame_touches` / `marker_scope_consume_touches` を減らす。

Codex へのタスク文:

```text
Continuation marker scope の close 判定を consumed frame の逐次伝播ではなく、cursor boundary event として扱う。

やること:
- ContinuationMarkerScope.frames_remaining を close_after_pops か close_at_cursor に置き換える、または内部変換層を追加する。
- enter_continuation_marker_scopes は active scope を close boundary 順で持つ。
- resume loop では frame pop 後に consumed_frames を進め、next boundary に到達した時だけ close_completed_marker_scopes を走らせる。
- request が innermost marker scope を外へ出る時、split_back は FrameCursor の suffix view を作るだけにする。
- request_close_offset の意味を cursor 座標で再定義し、既存テストに加えて nested marker / handler / adapter / continuation reuse の canary を追加する。
- ScopeState indexed marking はこの段階では production 化しない。shadow assert だけ使う。
```

この段階の期待 counter:

```text
marker_scope_consume_calls: 減る、または残しても軽くなる
marker_scope_consume_touches: 大幅減
marker_scope_frame_touches: 大幅減
marker_scope_close_pops: ほぼ同じ
marker_scope_request_closes: ほぼ同じ
request_resume_steps: 同じ
active_add_scans: 同じ
marker_frame_pushes: 基本同じ
```

---

## 最終判断

**まず A: immutable snapshot + resume cursor + segmented frame view。**

`Rc<[SharedFrame]> + range/cursor` は方向として当たり。ただし、`VecDeque` をそのまま slice に置き換えるんじゃなくて、

```text
stored snapshot は immutable
resume は cursor
request continuation は owned/segmented view
split/prepend は view 操作
marker scope は cursor boundary
```

という分離で入れるのがよさそうだねぇ。

これなら、handler hygiene と multi-shot を守りつつ、まず `continuation_frames_cloned` / `continuation_marker_scopes_cloned` の実コピーを狙える。`marker_frame_pushes` と `active_add_scans` は別の敵だから、snapshot 化の成果判定に混ぜない方がいいよ〜。

---

## Codex review notes

この方針は概ね採用する。
特に、stored continuation と resume cursor を分ける点、
flat `Rc<[SharedFrame]>` ではなく segmented view を前提にする点、
active marker / add-id marker の順序を snapshot 側へキャッシュしない点は現行 VM と整合している。

補正点:

- marker scope の per-scope decrement は、2026-06-27 時点で
  `close_at_frame` + resume-local consumed-frame counter へ置き換え済み。
  そのため、第3段階は「まず入れるべき本命」ではなく、
  `close_completed_marker_scopes` 呼び出しや remaining 計算をさらに event 化できるかを見る後続課題とする。
- `ContinuationFrames` / segment view の hot path には `request_resume_steps` 回の分岐が乗りうる。
  第1段階は Owned-only wrapper に留め、既存 runtime と counters が変わらないことを gate にする。
- one-shot continuation 判定は runtime の参照カウントや形だけで推測しない。
  `Runtime.continuations` に格納された first-class continuation は multi-shot snapshot 固定とする。

2026-06-27 実施済み:

- `Continuation.frames` を `VecDeque<SharedFrame>` 直持ちから `ContinuationFrames` wrapper へ変更した。
- wrapper は現時点では `VecDeque` を内包するだけで、snapshot / segment は未導入。
- `push_frame`, `push_continuation_frame`, `resume`, `finish_inline_request`,
  marker scope close の `split_back` / `prepend` を wrapper API 経由にした。
- `cargo test -p control-vm`, `YULANG_VM_SCOPE_STATE_SHADOW=1 cargo test -p control-vm`,
  `cargo test -p yulang --test cli`, `cargo build -q -p yulang --release` を通した。
- 100x nondet cache-hit では `runtime_execute` が 2.925s, 2.989s, 3.250s。
  `continuation_frames_cloned`, `continuation_marker_scopes_cloned`,
  `marker_scope_frame_touches`, `path_prefix_checks`, `active_add_scans` は baseline と同じ。

次の実装単位:

1. `Runtime.continuations` に格納する first-class continuation を `StoredContinuation` に分ける。
2. capture 時に owned `ContinuationFrames` を immutable snapshot 化し、invoke 時は cursor を作る。
3. `continuation_frames_cloned` を actual copied handles と logical observed frames に分ける。
4. request 中の `split_back` / `prepend` を flatten しない segmented view へ寄せる。
