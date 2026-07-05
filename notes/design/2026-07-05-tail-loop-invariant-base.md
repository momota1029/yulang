# Tail loop の不変基準面拡張（2026-07-05、Claude 署名・ユーザ承認済み）

状態: 承認済み（2026-07-05、ユーザ「あなたの判断を尊重します」）。確定した決定:
1. 入場条件の一般化（空 → 基準面一致）を採用する。
2. 一致判定は**同一性一致**（深さ一致では不十分）。
3. 段階は **Stage T1（shadow・挙動変更なし）を先行**し、棄却理由の分布を確認してから T2（実行）へ。

## 背景（確定した計測事実、HEAD = bd2a78fe、release）

- 純粋な range fold は 38ce176c の tail loop に乗る: N=100,000 で max_active_frames_len=3、add_id scan 0。
- しかし body に state-ref 更新があると（`for i in 1..N: &total = $total + i`、および明示 `fold`+ref も同じ）:
  - max_active_frames_len ≈ N、max_active_add_ids_len ≈ 2N、active_add_id_scans ≈ N²。
  - N=65,536 の平坦ループで stack overflow（runtime timings すら出ない）。
  - 完走域の実測: N=4,096 で 136ms、N=32,768 で 3.62s（scan 10.7億回）。
- 入れ子 20×20 ベンチ（loop_for_sum_ref_20_discard）が速く見えるのは各ループの辺が短く蓄積が浅いだけ。二次爆発の本丸は平坦な長いループ。

## 真因

1. `for` は `std::control::flow::loop::for_in` → `xs.fold` → `fold_ints` 末尾再帰（lib/std/data/range.yu:51）に脱糖される。
2. body が効果つきだと `f acc i` の末尾適用引数が `ApplyArg` continuation になり（runtime.rs ~15069）、resume は `apply_scoped_value_result` 経由（~16290）で、marker frame の継続処理の内側から再帰呼び出しに入る。
3. 38ce176c の tail loop 入場条件（~15154）は「active frame / add_id / marker plan / provider / state / handler が全部空」を要求するため、この経路は毎反復棄却される。
4. 反復ごとの marker frame（`next::sub`/`catch` 由来、frame 1 + add_id 2）が pop より先に再帰へ進むため退役されず、N 段積み上がる。

## marker 退役だけでは足りない（2026-07-05 Codex 試作の結果）

反復ごとの marker frame を末尾位置で退役させても、tail 適用地点には
`frame=11 handler=5 add=17 plan=8 provider_env=1 provider_handlers=11 state=1 host_root=true`
という**ループ不変の土台**が残る。内訳は `for_in` の `last::sub`/`next::sub`/`loop`/`catch` の足場と、`my $total` の state handler 本体。これらはループ全体の寿命を持つ正当な dynamic scope であり、退役対象にできない。ゆえに「全部空」条件のままでは、この経路は永遠に loop に乗れない。

試作は revert 済み（commit なし）。試作時の安全述語（再利用可）:
- 最内 active marker frame のみ対象
- source が `ContinuationResume` / `MarkedForce`
- `handler_path == None`
- depth 0 の active AddId が存在
- `carry_after_frame == true` の AddId が存在しない（9d10af50 の hygiene 分類に従う）

## 提案: 入場条件を「空」から「基準面一致」へ

tail loop の入場条件を次のように一般化する:

- 同一 closure への最初の tail 呼び出し時点で、各 active stack（frames / add_ids / marker plans / provider env / provider handlers / state handler frames / handler stack / host branch）の**基準面スナップショット**を取る。
- 以後、同一 closure への tail 呼び出しで、現在の各 stack が基準面と一致するなら、再帰の代わりに loop する。
- 反復ごとの marker frame は上記の安全述語で末尾位置退役し、各反復が基準面へ戻れるようにする（退役は loop 化の前提条件）。

### 安全条件

1. **一致は深さでなく同一性**で判定する（基準面より上が空になっただけでなく、基準面の frame/add_id がすり替わっていないこと）。深さ比較だけだと pop→push で別 scope が同じ深さに来た場合を誤認する。
2. **基準面より上を参照する continuation が捕獲されて生存していないこと**。known-state direct ops（KnownHandlerPlan::State の direct get/set）は continuation を実体化しないので安全。nondet / multi-shot 等で continuation が実体化・escape した反復では loop してはならない（その反復は従来経路へフォールバック）。
3. own-path guard / foreign carried guard の扱いは 9d10af50 の分類に従う。foreign carried guard が居る frame は退役も loop も対象外。

### 段階（既存の staging 文化に従う）

- **Stage T1（shadow、挙動変更なし）**: 判定だけ実装し counter で計測。
  - `tail_invariant_base_would_loop` / `tail_invariant_base_rejected`（棄却理由の内訳つき: 同一性不一致 / continuation 実体化 / carried guard）。
  - 平坦 for+ref・fold+ref・nondet 系・file 系の代表で would_loop 率と誤検知ゼロを確認。
- **Stage T2（実行）**: T1 で棄却理由の分布が設計どおり（安全条件由来のみ）であることを確認してから loop 化を有効化。
  - 門番 fixture（無改変で green 必須）: `file_ref_lines_each_update_chain_native`、`do_binding_state_protocol`、`file_text_with_commit_do`、nondet 系一式。
  - 新 canary: 平坦 for+ref N=4096 で max_active_frames_len が小さい定数に張り付くこと。明示 fold+ref 同様。負例 canary（carried guard あり）で loop しないこと。
  - 受け入れ計測: N=65,536 / 1,048,576 の平坦 for+ref が stack overflow せず、時間が N に線形。

### 決定点（ユーザ確認事項）

1. tail loop の入場条件の一般化（空 → 基準面一致）を認めるか。
2. 一致判定の強度: 深さ一致で足りるとみるか、同一性一致（推奨）まで要求するか。
3. Stage T1 shadow を挟むか、T1+T2 を一息にやるか。

## 関連

- 38ce176c（tail loop 初版・空条件）/ bd2a78fe（thunk-wrapped state handler 認識）/ 9d10af50（marker hygiene 分類）
- notes/design/2026-06-30-known-state-handler-plan.md（state direct ops）
- notes/design/2026-07-02-static-route-promotion-plan.md（TailResumptive × StaticHandler の静的側。本提案は動的側の対）
