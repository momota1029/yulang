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

## 2026-06-24 follow-up: effect dispatch / marker scope measurement

`Value::EffectOp` と `Thunk::Effect` に `InternedPath` を持たせ、effect request 発行時の path
intern を避ける変更を測った。結論として、この最適化は構造としては妥当だが、実時間への寄与は
ほぼ測定ノイズ内だった。

`bench/nondet_20_discard.yu` の `hyperfine` 比較:

```text
artifact execution:
  current: 31.4ms ± 0.9ms
  parent:  31.4ms ± 1.3ms

cached source:
  current: 39.8ms ± 1.1ms
  parent:  38.5ms ± 1.3ms

no-cache source:
  current: 620.2ms ± 13.3ms
  parent:  635.7ms ± 14.5ms
```

`each 1..20 + each 1..20` を 100 回繰り返す一時 workload では、artifact execution は
`current 6.447s ± 0.090s`、`parent 6.494s ± 0.116s` で、改善は約 1% 程度だった。

同 workload の runtime stats:

```text
run.runtime_execute: 5.988s
run.effect_requests: 86961
run.active_add_scans: 16556526
run.active_frame_scans: 0
run.path_prefix_checks: 16556526
run.path_eq_checks: 260883
run.request_resume_steps: 1533382
run.marker_scope_frame_touches: 57242962
run.marker_scope_consume_touches: 57242962
run.marker_scope_max_depth: 105
run.continuation_frames_cloned: 6424307
run.continuation_marker_scopes_cloned: 8068284
```

この結果から、path interning / path equality 自体よりも、次の二つが支配的である。

1. `Runtime::mark_request_with_active_markers` が request ごとに `active_add_ids` を全走査する。
   上の workload では 1 request あたり平均約 190 個の active add-id marker を見る。
2. `consume_marker_frame` が continuation resume の各 step で active marker scope 全体を触る。
   `marker_scope_frame_touches` は 57M を超え、scope depth は最大 105 まで伸びている。

ただし、`consume_marker_frame` を単純な global consumed-frame counter に変える実験は採用しない。
意味上は「各 scope の `frames_remaining` を毎 step decrement」から「読み取り時に消費数を差し引く」
へ置き換えられるが、同条件での直接比較はむしろ悪化した。

```text
marker cursor experiment:
  changed:    6.462s ± 0.116s
  clean HEAD: 6.376s ± 0.155s
```

この変更はテスト上は通ったが、実時間で効果がなく、コードも引数伝播を太らせるため戻した。
今後同じ形で再試行しない。

`active_add_ids` の path index 化も単純ではない。`AddIdMarker` は次を同時に持つ。

- own path に効くか (`guard_own_path`)
- foreign path に効くか (`guard_foreign_path`)
- frame を抜けたあとも carry するか (`carry_after_frame`)
- marker entry 時点で既に excepted だった request を repaint しない条件

したがって、`path -> markers` の hash index だけでは foreign-path marker と entry-time guard
条件を扱いきれない。次に本気で削るなら、`Request.guard_ids` と `carried_guards` を
毎 request の `Vec` 構築として扱うのをやめ、guard set / exposed set / handler boundary を
scope snapshot 側の persistent state へ寄せる必要がある。

ref update だけを見るために `for` loop で大量更新する一時 workload も試したが、
100 回程度でも release binary が stack overflow した。これは今回の path-key 最適化とは別の
runtime stack safety 問題として扱うべきで、VM micro-benchmark としては使わない。

当面の結論:

- path key 化は構造上の整理としては残してよいが、速度改善としてはほぼ終わり。
- micro optimization より、`Request.guard_ids` / `carried_guards` / marker scope snapshot の
  表現を変える設計が必要。
- その設計に入るまでは、control VM 高速化より hardening / public docs / golden test を優先する。
