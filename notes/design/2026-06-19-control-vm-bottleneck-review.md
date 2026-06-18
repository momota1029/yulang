# control VM bottleneck review - 2026-06-19

現状の `runtime_execute` は、`bench/nondet_20_discard.yu` が 46〜49ms、
`examples/showcase.yu` が 100〜111ms 前後。旧 control VM の 10ms 前後とはまだ 5倍前後離れている。

## Claude review

- 最本命は `CapturedEnv`。
  現行は `Rc<HashMap<DefId, Value>>` + `Rc::make_mut` で、`env.clone()` 後の bind / let / lambda apply で
  HashMap 全体の COW clone が発火しやすい。
- 改善案は parent pointer chain。
  scope ごとに少数の `(DefId, Value)` binding を持ち、clone は親 `Rc` 共有、insert は local push にする。
  lookup は local reverse scan から parent を辿る。
- 優先順位:
  1. `CapturedEnv` の parent/scope-chain 化
  2. `Value` / request 周辺の clone 削減
  3. marker / handler scan の ScopeId 化
  4. 完全 trampoline 化
  5. 残りの Type / Pat table 化
- 見立てでは `CapturedEnv` だけで 2〜3x、`Value` clone 削減と合わせて 10ms 台が射程に入る可能性がある。

## ChatGPT Pro review

- 一つ選ぶなら `Value` / thunk / closure 周辺の cheap-clone 化。
  ただし実際には `Value` handle 化と `CapturedEnv` dense/scope-chain 化をセットで見るべき。
- 旧 VM にも COW env はあったため、COW だけが 5倍差の説明ではない。
  旧 VM との差は、control value が shallow handle で、dense local ID と inline frame を使っていた点。
- 最初に Rc 化する候補:
  1. `Closure(Rc<Closure>)`
  2. `Thunk(Rc<Thunk>)`
  3. `FunctionAdapter(Rc<FunctionAdapter>)`
  4. `Marked` marker payload の共有化 / ScopeId 化
  5. `Record` / `Tuple` / poly payload の `Rc<[Value]>`
  6. effect path / record field name / string payload の ID 化
- `fr_unwrap == 0` でも frame allocation は消えていない。
  現行の `VecDeque<Rc<Frame>>` は通常 path でも frame ごとに allocation / refcount / pointer chasing を払う。
  current stack は inline `Vec<Frame>`、captured continuation だけ persistent snapshot にする方向が旧 VM に近い。
- ScopeId は scan 削減だけなら過大評価。
  本命は marker plan push/pop、scope array prepend、`frames_remaining` 更新、request guard Vec 再構築を
  scope pointer 遷移へ置き換えること。
- static payload table の残りは二次的。
  単純な `PatId` ではなく、binder を `PatPlanId + pc` にするなら env dense slot 化と合わせて価値が出る。

## Synthesis

次の大きい候補は `CapturedEnv` と `Value` の組み合わせ。
どちらが先かは意見が分かれるが、両者は増幅関係にある。
`CapturedEnv` の HashMap COW は大きい `Value` clone を増幅し、`Value` が重いままだと env 改修の効果も取り切れない。

次の slice は、いきなり大改造せず、まず counter を足して支配項を確認する。

- `env_inserts`
- `env_cow_clones`
- `env_cow_entries_copied`
- `env_lookup_steps` または `env_lookup_hits`
- `value_clones_by_variant`
- `frame_allocs`
- `marker_scope_frame_touches`

その後の実装候補:

1. `Closure` / `Thunk` / `FunctionAdapter` の cheap-clone handle 化を小さく試す。
   `ListTree` 自体はすでに `Rc<Value>` を使っているため、まず制御値から見る。
2. `CapturedEnv` を parent pointer chain へ寄せる。
   最終形は dense local slot だが、まず HashMap COW clone を消す小さい形で効果を見る。
3. current stack と captured continuation snapshot を分ける。
   通常実行では inline `Vec<Frame>`、multi-shot capture だけ persistent snapshot 化する。
4. marker / handler state を ScopeId 風の persistent scope node に寄せる。
   目標は scan counter だけでなく、push/pop と resume 中の scope touch を減らすこと。
5. dense env と合わせて `PatPlanId` 化を検討する。

現時点では、単純な式 arena 化や残り static payload ID 化だけで 46ms -> 10ms を狙うのは弱い。
旧 VM に近づける主軸は、cheap-clone control value、env layout、inline current frame、scope snapshot の四つ。
