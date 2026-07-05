# MarkedForce 同一マーカー再入融合 計画（2026-07-05、Claude 署名・F2 まで landed・push 済み）

状態: **F2（実行）まで landed**（commits 9ba94c4e / 373b61ac、push 済み・origin/main = 373b61ac）。確定した決定:
1. 「同一マーカー再入融合」の方向性を採用する。
2. トランポリン化は **MarkedForce 専用の小さいループ**として置く（既存 38ce176c tail loop とは合流させない——仕組みを混ぜると invariant-base 同様の深い罠を再び踏みやすいため）。
3. **Stage F1（shadow・挙動変更なし）を先行**し、再入一致率の分布を確認してから F2（実行）へ。

## 追記4（2026-07-05 夜、Claude 署名）: F2 landed——平坦 for/state ループの overflow 根治

ユーザ承認（「進みましょう！」）を受けて F2 を実装。安全ゲートは追記3で確定したとおり **`Rc::ptr_eq`（marker identity 一致）AND `marker_identity_was_materialized() == false`（per-marker 履歴、世代差分の近似は不使用）**を毎反復再チェックする形で実装（`marked_force_can_fuse_tail_reentry`）。機構は静的 peek ではなく `MarkedForceTailStep`（`Result` / `Reenter` / `ContinueSameEnv` / `ContinueOwnedEnv`）を返すトランポリンとして実装（`force_marked_value_tail_loop`）——frame は一度だけ push、safety gate が成立する限りループで使い回し、不成立になった時点で通常の再帰 push にフォールバック。

**成果（release 実測）**:
- 平坦 `for`+ref・明示 `fold`+ref・no-ref `for` の全形状で **N=1,048,576 が overflow せず完走**（本日ずっと倒れていたサイズ）。for+ref: 16.165s、fold+ref: 8.369s、no-ref for: 12.783s。
- N=65,536 の deep-profile gauge: `max_active_frames_len=13`、`max_active_add_ids_len=21`——**N に対して定数**（以前は N に比例して成長）。`fused=65537` が反復のほぼ全数で融合が実際に効いたことを示す。
- スケーリングはおよそ線形（65,536→1,048,576 で比率どおり）。ただし反復単価は純粋 fold（~2.9μs/iter）よりまだ高め（for+ref ~15.4μs、fold+ref ~8.0μs、no-ref for ~12.2μs）——**stack/frame 成長は根治したが、VM オーバーヘッドそのものは別の課題として残る**。
- 決定的 adversarial 形状（追記3の入れ子 each、unsafe_materialized=21 を生む形）を **正しさの回帰 fixture** として追加（`marked_force_nondet_materialized_tail_reentry.yu`）——flag-off/deep-profile 両方で `compare.control: match`、かつ 21 件は正しく融合されず（`fused=2` のみ）通常経路にフォールバックしたことを確認。
- 既存 named canary（`file_ref_lines_each_update_chain_native` / `do_binding_state_protocol` / `file_text_with_commit_do` / `debug_runtime_evidence_run_known_state_frame_matches_control_across_nondet_resume`）は無改変で green。release contract（refs 47 / std.nondet 18 / file 73）も green。
- Claude 検品済み: 既存テストは無改変（新規テスト追加のみ、cli.rs diff で確認）、Codex は push せず待機（fetch+status で確認）。Claude が push 実施（`b7c1c72b..373b61ac`）。

**残課題**: 反復単価の VM オーバーヘッド縮小（fold との差）は本ノートのスコープ外——別途の性能課題として扱う。

## 背景

Stage S（ba618206〜a18afa41、push 済み）で state get/set の perform-site 短絡が landed し、継続生成は全ループ形状でゼロになった。しかし平坦ループ（`for i in 1..N: &total = $total + i`、明示 `fold`+ref、no-ref `for` すら）は依然 N≈65,536 で stack overflow する。同日の顕微鏡トレースで、残る唯一の蓄積源は **MarkedForce frame**（反復あたり frame 1 + add_id 2）と確定した:

- ref 系: `&total#1:0` の marked callback thunk force
- no-ref for 系: `std::control::flow::loop::last` の force

いずれも同一の Rust コード経路を反復ごとに通る: `force_thunk_result` の `Marked` 分岐（runtime.rs:20511）が
`with_marker_frame(EvidenceMarkerFrameSource::MarkedForce, markers.clone(), true, None, |runner| runner.force_thunk_result(value.clone()))`（runtime.rs:20537）
で包まれる。

## 真因（本日の追加調査で確定）

`with_marker_frame` は「push → closure 実行 → pop」という形:
- push: `push_marker_frame`（runtime.rs:11397）が `active_frames` と depth-0 の `active_add_ids` を積む。呼び出しは runtime.rs:11010/11024。
- closure 実行: runtime.rs:11026。
- pop: `pop_marker_frame`（runtime.rs:11437）が `active_frames` / `active_handler_frames` / `active_add_ids` / `active_marker_plans` を切り詰める。呼び出しは runtime.rs:11040。

closure の中身が論理的に末尾呼び出しで終わっていても（`fold_ints` は自身を末尾再帰——定義 lib/std/data/range.yu:51、再帰呼び出し range.yu:53 `fold_ints(f, i + 1, end, f acc i)`、no-ref for 経路は range.yu:67）、その再帰呼び出しは**`with_marker_frame` という Rust 関数本体の末尾位置ではない**。pop は closure が return してから走る設計だから、closure の中でさらに一段深い `fold_ints` 呼び出しが同じ `MarkedForce` を経由すれば、その pop は「もっと深い pop が先に済むまで」保留される。bookkeeping の Vec と実 Rust コールスタックの両方が、反復ごとに一段ずつ積み増す。

これは「tail loop の入場条件が空を要求する」という表層の話ではない——invariant-base 提案（notes/design/2026-07-05-tail-loop-invariant-base.md）が踏んだ罠はここにある。**with_marker_frame 自体の形が、内側にどんな末尾呼び出しがあっても Rust レベルで非末尾再帰にする**という、一段深いところに真因がある。だから「frame を末尾位置で退役する」だけでは届かない。今朝の invariant-base T2 試作で frame 退役後も identity_mismatch が残った理由も、これで説明がつく——退役しても `with_marker_frame` の Rust スタックフレーム自体は closure の return を待ち続けている。

本日確認した補足事実（file:line）:
- pop は Rust closure の return に厳密に紐付く。事前 peek 機構は存在しない。`try_force_continuation_apply_expr`（runtime.rs:14917）と `runtime_expr_cache` の force-effect fusion（runtime.rs:9054）は別目的の特定パターン専用で、marker frame の pop タイミングには関与しない。tail-invariant shadow（runtime.rs:15966）は計測専用で pop はしない。
- tail loop 入場ゲート（runtime.rs:15568）は `active_frames` / `active_handler_frames` / `active_add_ids` / `active_marker_plans` / `active_provider_envs` / `active_provider_handlers` / `active_state_handler_frames` / `host_scheduler.has_only_root_branch()` を要求。`MarkedForce` は `handler_path = None` を渡すため `active_handler_frames` は増えないが、`active_frames`・`active_add_ids`・`active_marker_plans` は増える。
- 9d10af50 の hygiene 分類を超える新規ハザードは見つからなかった。この `MarkedForce` では `handler_path = None` のため `handler_boundary_for_request_parts` は早期 return（runtime.rs:13870）。force return 後・次の末尾呼び出し前に意味のある marker 状態を読む箇所は他に見当たらない。

## 提案の方向: 「退役」ではなく「同一マーカー再入の融合」

一般化した tail loop 入場条件ではなく、**MarkedForce という construct 自体を対象にした特化融合**を提案する。

- ある `MarkedForce` が forcing 中に、その評価が末尾位置で**同一 identity の marker 集合**を持つ別の `MarkedForce` を再度開始しようとしたら——それは意味的に「同じスコープの次の反復」であって「新しい入れ子スコープ」ではない。
- この場合、新しい push を行わず、既存の frame/add_id/plan を**そのまま使い回す**。pop は「次の反復が同一 identity の `MarkedForce` を作らなかった」時点まで一回だけ遅延する。
- 実行系としては、`force_thunk_result` の中の「同一 identity 再入」を Rust 関数呼び出しではなくトランポリンのループへ変換する必要がある——`with_marker_frame` 自体をループ対応の形に作り替える。

同一性判定は `markers` の実体（Rc/ポインタ identity）で行う。invariant-base の「同一性一致」原則をここでも踏襲するが、対象を「全 active stack」ではなく「このひとつの marker 集合」に絞る。範囲が狭い分、9d10af50 が扱った hygiene 問題（foreign carried guard 等）を踏む可能性も invariant-base 案より下がると見ている。

### 安全条件（案、実装前に要検証）

1. 再入検出は「force 中に、同一 marker identity の `MarkedForce` が呼ばれようとした」時点で行う。値の中身ではなく `markers` の identity で判定。
2. 再入の間に、退役済み frame の内容を参照する継続が実体化・escape していないこと（invariant-base と同じ懸念、9d10af50 分類を流用）。
3. 再入呼び出しが真の末尾位置であること——Yulang 意味論上の末尾であるだけでなく、`force_thunk_result` の呼び出し構造上もその先に追加の作業が残っていないこと。

### 未解決の設計課題（決定点）

1. `force_thunk_result` / `with_marker_frame` をトランポリン化する具体的な形——どこにループを置くか。既存 38ce176c tail loop と合流させるか、`MarkedForce` 専用の小さいループにするか。
2. 「同一 identity の再入」をどこで検出するか——force の呼び出し前（prospective）か、再帰が一段進んでから引き返して判定するか。
3. Stage 分け: F1 shadow（同一 identity 再入の発生率を計測するだけ、挙動変更なし）を先行するか。

## 段階案

- **Stage F1（shadow、挙動変更なし）**: 「force 中に同一 marker identity の `MarkedForce` が末尾位置で再度開始されたか」を counter で計測。平坦 for+ref・fold+ref・no-ref for・nondet 系・file 系で再入一致率と誤検知ゼロを確認。
- **Stage F2（実行）**: F1 で分布が期待どおりなら、frame 使い回し＋トランポリン化を実装。
  - 門番 fixture: 既存の `file_ref_lines_each_update_chain_native` / `do_binding_state_protocol` / `file_text_with_commit_do` / `debug_runtime_evidence_run_known_state_frame_matches_control_across_nondet_resume` ＋ 本日追加の 3 canary（`for_ref_tail_known_state_4096` 等）。
  - 受け入れ: 平坦 for+ref が N=65,536 / 1,048,576 で overflow せず、時間が N に線形。

## 追記（2026-07-05、Claude 署名）: F1 shadow 実装と「Rc identity 単独では不十分」の確定

- **Stage F1 landed**（`cb42c0da Add MarkedForce reentry shadow counters`）。deep-profile flag 配下、flag-off は counter 全ゼロ・release timing 回帰なし（N=4096 で 96.2ms、従来レンジ内）。
- ref 系・no-ref for 系ともに `marked_force_reentry_same_identity` が支配的で N に比例——再入融合の対象は実在し支配的と確認。
- **しかし `bench/nondet_20_discard.yu` でも `same_identity=861`** が発生。最小例 `each 1..1` で切り分けたところ、`same_identity=3` の中に **`k(true)` と `k(false)` という論理的に別の nondet 分岐**が同一の continuation marker Rc を共有しているケースが含まれると確認された（`.list` が `merge k(true).list k(false).list` で同じ `k` を 2 回 resume するため）。
- **結論: Rc identity 単独は安全条件として不十分**。設計ノート本文の安全条件 2（「retire 対象 scope に対して継続が実体化/escape していないこと」）は必須であり省略できない。
- 好材料: `record_continuation_materialized()` という機構が既存で、`.list` が `k` を束縛する瞬間に発火することを確認済み。この機構を使えば nondet の unsafe ヒットを弾き、ref-loop/fold の safe ヒットのみ通せる見込み。
- **次の一手（F1 精緻化、まだ shadow のまま）**: `same_identity` を「継続実体化なし＝safe」「継続実体化あり＝unsafe」に分割 counter 化し、ref/fold/no-ref-for が全て safe 側、nondet が unsafe 側に落ちることを確認してから F2（実際の frame 使い回し）に進む。

## 追記2（2026-07-05、Claude 署名）: F1 精緻化の結果、当初の危険仮説は事実誤認と判明

- **F1 精緻化 landed**（`bbfd002b Split MarkedForce reentry shadow counters`）。継続実体化チェック（`record_continuation_materialized` による `continuation_capture_generation` 監視）を追加。ref/fold/no-ref-for は 100% safe、`bench/nondet_20_discard.yu` は `861 / 0 / 21 / 441`——**unsafe が実測ゼロ**という、追記1の予想（nondet に unsafe 分布があるはず）と矛盾する結果が出た。
- 矛盾を推測で済ませず、`each 1..1` 最小例で個別ヒットまで遡って再調査。結果、**追記1の危険仮説自体が事実誤認**と判明:
  - `each 1..1` の 3 件の `same_identity` ヒットは、いずれも `k(true)`/`k(false)` 分岐 resume より**前**に起きる、branch 条件評価・junction wrapper 内の同一分岐上の force であり、continuation 実体化はその後（全 MarkedForce shadow frame が pop され stack が空になった後）に起きる。
  - `k(true)`/`k(false)` の resume は `EvidenceContinuationFrame::MarkerFrame`/`resume_marker_frame` という**別経路**を通り、**異なる marker identity**を持つ。親 MarkedForce frame が active な状態で `force_thunk_result` の `Marked` 分岐に再入することはない——ゆえにこの経路は `same_identity` としてカウントされることが構造的にない。
  - 結論: `each 1..1` については、追記1で懸念した「`k(true)`/`k(false)` が同一 marker Rc を共有し same_identity として誤ってカウントされる」という危険シナリオは**発生しない**。F1 の safety signal は不健全ではなかった。
- **ただし一般化はしない**——この結論は `each 1..1` という最小例で確認された事実であり、`bench/nondet_20_discard.yu` 全体（861 件）や他の nondet 形状すべてで cross-branch fusion が起きないことを網羅的に証明したわけではない。F2 着手前に、より広い nondet ワークロードでの確認が望ましい。
- **現在地**: F1（shadow、精緻化込み）は committed・green・挙動変更ゼロ確認済み。F2（実行）着手前に、(a) より広い nondet 網羅確認を追加するか、(b) 現状の証拠で十分とみて F2 に進むか、ユーザ判断待ち。

## 追記3（2026-07-05、Claude 署名）: 意図的破壊テストで unsafe ケースを実発見——F2 の安全ゲート仕様が確定

ユーザ指示（「石橋を叩き割る勢いで、つまり慎重に」）を受け、F1 の既存 shadow 計装（追加コード変更なし、`--runtime-evidence-profile-deep` での計測のみ）を使って、意図的に unsafe ケースを誘発する 5 形状を構築・計測した。

- (a) fold+branch()（同一ループ内混在）: `8190 / 0 / 0 / 8191` — safe。
- (b) ref+branch() 混在（既存 canary の拡大版）: `196607 / 0 / 131071 / 458747` — safe。
- (c) **外側 `each` の各分岐内に、同一 identity で末尾再帰する内側 fold を持つ形**: `16372 / 21 / 1 / 16385` — **unsafe_materialized = 21 実測**。
- (d) 1 反復内に複数の逐次 `branch()`（深い choice tree）: `43690 / 0 / 0 / 131071` — safe。
- (e) `junction::junction(any/all ...)`: `14 / 0 / 6 / 6` — safe。

### 決定的な発見（(c)）

21 件の unsafe ヒットを個別追跡した結果、**`gen == parent_gen`**（「外側 MarkedForce 開始から継続実体化世代が変わったか」という粗い判定では素通り）だったが、`marker_materialized = true`（「この marker identity 自体が、過去いずれかの時点で実体化した継続に運ばれたことがあるか」という **per-marker 履歴フラグ**）で正しく unsafe と分類された。つまり:

- **「世代が変わったか」という粗いチェックだけでは、この (c) のような入れ子 choice を見逃す**。
- F1 精緻化（bbfd002b）で実装した `marker_materialized` の per-marker 履歴追跡は、狙った以上に正確な粒度で機能していた。
- **結論: F2 の安全ゲートは `marker_identity 一致 AND marker_materialized == false`（per-marker 履歴ベース）を必須とする。「outer force 開始からの世代差分」のような粗い近似では不十分**——(c) が反証になる。

### 評価

5 形状中 4 つが safe、1 つ（(c)）で実際に unsafe を検出——これは「何も起きなかった」という弱い証拠ではなく、「危険な形を作ったら正しく捕まった」という強い証拠。ただし探索した形状は 5 通りのみであり、nondet 全空間の網羅ではない。F2 実装時は `marker_materialized` の per-marker 履歴チェックを安全ゲートの必須項とし、このチェックを外した近似（世代差分など）に置き換えないこと。

## 関連

- [[perf-findings-2026-07-05]]
- notes/design/2026-07-05-tail-loop-invariant-base.md（invariant-base 提案・T2 revert の顛末、本ノートの前段）
- 38ce176c（tail loop 初版）/ bd2a78fe / 9d10af50（marker hygiene 分類）
- ba618206〜a18afa41（Stage S: known-state perform-site 短絡、本ノートの前提）
