# Performance Localization Plan

Yulang の性能改善は、意味論を削る作業ではなく、意味論上必要なコストを
「変更された source」と「実際に動的な effect 境界」へ局所化する作業として進める。

普通の使用感は目標にできる。ただし次の三つは本質的な重さとして残る。

- clean build の principal-style 型推論
- 動的な multi-shot continuation
- 実際に枝を列挙する nondeterminism

一方で、次は意味論上不可避ではない。

- 変更していない std / dependency SCC の再 parse / lower / infer
- generalize の restart ごとの同じ graph 再走査
- request ごとの全 marker 線形探索
- pure code を generic handler VM で実行すること
- var-var replay の同じ transitive consequence の再物質化

## Guardrail

高速化は hardening の後に置く。

必ず守ること:

- `docs/infer-solver-invariants.md` の public type boundary / handler hygiene を壊さない。
- `compose_for_replay()` に `pop(n) -> pop(1)` clamp を戻さない。
- var-var routing は、generalization / public projection が読める evidence を保存するまで本番 skip にしない。
- runtime marker の path-only index 化を本命にしない。foreign-path / entry-time guard 条件を失う。
- pure / direct-style island や native backend は、cache と runtime scope state の後に回す。

## Release Gate First

最初に、性能変更前後を比べる一つの release gate script を作る。

現在の入口:

```text
scripts/performance-gate.sh
```

含めるもの:

- public signature canary
- adversarial corpus
- playground smoke
- runtime smoke
- `check-poly-std examples/showcase.yu`
- cached / no-cache `run --print-roots bench/nondet_20_discard.yu`
- runtime marker-heavy workload

最低限見る指標:

- `infer`
- `constraint.drain`
- `analysis.quantify_generalize`
- `analysis.generalize_*`
- `constraint.replay_*`
- `run.runtime_execute`
- `run.active_add_scans`
- `run.request_resume_steps`
- `run.marker_scope_frame_touches`
- `run.continuation_*_cloned`

成功条件:

- 新しい高速化を入れる前に、current HEAD の cold / warm baseline が保存されている。
- 以後の性能 commit は、この gate の増減を一行で説明できる。

2026-06-25 の baseline:

```text
target/performance-gate/20260625-105747/summary.txt
```

この run は hardening smoke / adversarial corpus / release smoke / source metrics /
static-analysis bench を通している。

実行結果は `target/performance-gate/<timestamp>/` に保存する。各 command の完全な
stdout/stderr は個別 log に残し、`summary.txt` へ wall time と主要 metrics を抜き出す。

既定では hardening smoke / adversarial corpus / release smoke / source metrics /
static-analysis bench を走らせる。個別に切りたい場合は次を使う。

```text
YULANG_PERF_GATE_HARDENING=0
YULANG_PERF_GATE_ADVERSARIAL=0
YULANG_PERF_GATE_RELEASE_SMOKE=0
YULANG_PERF_GATE_SOURCE_METRICS=0
YULANG_PERF_GATE_STATIC_BENCH=0
```

## Phase 1: Compiled-Unit Cache To Normal Path

最優先。推論器をさらに細くするより、触っていないコードを推論しない方が効く。

既存の whole-program `.yuir` / `.yuvm` artifact cache は便利だが、目標は
source dependency SCC ごとの compiled-unit cache である。

根拠:

- `spec/2026-06-14-control-artifact-cache.md`
- `notes/design/partial-compilation-cache-plan.md`
- `notes/design/source-realm-band-plan.md`
- `notes/todo/static-analysis-speed.md`

順番:

1. 現行 cache の cold / warm / no-cache timing を release gate に入れる。
2. `CompiledUnitManifest + CompiledSyntaxSurface` を source SCC から出す。
3. cached operator syntax で downstream source を parse できるようにする。
4. `CompiledNamespaceSurface` を入れ、dependency source を lower せず名前解決できるようにする。
5. `CompiledTypedSurface` を入れ、dependency body を lower / infer せず scheme を使う。
6. `CompiledRuntimeSurface` を入れ、dependency core/runtime binding を merge する。
7. std bundle を wasm / playground build に入れ、初回 run で std source compile を避ける。
8. user dependency SCC cache へ広げる。

2026-06-25 status:

- Done: `sources::CompiledSyntaxSurface` stores public / our parser-facing
  operator exports and reexporting `use` declarations without dependency CSTs.
- Done: `sources::load_suffix_with_syntax_prefix` can parse downstream source
  using only a serialized syntax prefix.
- Done: `yulang::cache` can read/write `.yuunit` compiled-unit envelopes with
  `CompiledUnitManifest` and syntax surface.
- Not done: source dependency SCC selection and normal-path cache hit import.
- Next: add `CompiledNamespaceSurface` so imported syntax can resolve to stable
  value/type/module identities during lowering.

撤退条件:

- source body を読んでいないのに operator syntax / namespace / role / effect lookup が通常 route とずれる。
- fake def や placeholder scheme を作り始めた。
- std 専用分岐として固定されそうになった。

最初の成功条件:

- cached dependency unit の operator export を使う downstream file が、dependency source を再 parse せず parse できる。
- entry file だけを編集した run が、std / unchanged dependency infer を払わない。

## Phase 2: Generalize Restart Locality

clean build で残る本命。現状は多数の単一 binding に対して、restart のたびに
compact / dominance / role projection をかなり再走査している。

目標は「generalize を速くする」ではなく、root ごとの同じ view を再構築しないこと。

順番:

1. root ごとの generalize restart summary を出す。
   - root id
   - restart reason
   - compact nodes / vars
   - dominance input count
   - role projection input count
2. `constraint epoch` を導入し、root summary が依存する var / bound / role input の epoch を記録する。
3. `root compact cache` を作り、involved-variable epoch が変わらない限り再利用する。
4. `dominance cache` と `role projection cache` を同じ方式で足す。
5. restart loop は view 全体を捨てず、dirty な view だけを再構築する。

やらないこと:

- 共起分析 / 極性消去に rigid / blocked pair / protected var set を足さない。
- テスト期待値を現在の表示に合わせて緩めない。
- `Any` / `Never` を未解決 fallback に使わない。

成功条件:

- `analysis.quantify_generalize` と `analysis.generalize_collect_dominance` が下がる。
- public signature canary と adversarial corpus が変わらない。
- restart count が同じでも、restart 後の総走査量が下がる。

## Phase 3: Runtime ScopeState

runtime 側の次の本命は path 比較ではなく、marker / guard / scope state の表現である。

根拠:

- `notes/design/2026-06-19-control-vm-bottleneck-review.md`
- `notes/design/control-vm-frame-runtime-plan.md`
- `spec/2026-06-13-runtime-guard-markers.md`

現在の太い項目:

- `active_add_ids` 全走査
- resume step ごとの marker scope touch
- continuation snapshot clone
- request ごとの guard / carried marker construction

方針:

```text
ScopeStateId
  -> parent
  -> handler delta
  -> guard delta
  -> exposed-set delta
  -> marker delta
```

request は毎回 `Vec<GuardId>` を作らず、現在の `ScopeStateId` と effect path から
「この request に見える guard / marker」を読む。

順番:

1. marker-heavy workload を release gate に固定する。
2. `Request.guard_ids` / `carried_guards` / active marker plan の allocation counter を追加する。
3. read-only `ScopeState` shadow を入れ、現在の linear scan と同じ marker decision になるか比較する。
4. shadow が安定したら、request marking の入口だけ `ScopeStateId` query に切り替える。
5. continuation snapshot は current stack と captured snapshot を分ける。
6. one-shot continuation は move / inline、multi-shot だけ persistent snapshot にする。
7. stack overflow 再現 workload を trampoline 化の gate にする。

撤退条件:

- foreign-path marker や entry-time excepted request を区別できない。
- scan counter は減ったが実時間が悪化する。
- scope state の更新が eval / apply の引数を太らせるだけになる。

成功条件:

- marker-heavy workload の `runtime_execute` が 20% 以上下がる。
- `active_add_scans` と `marker_scope_frame_touches` が構造的に下がる。
- nondet / callback hygiene の runtime canary が変わらない。

## Phase 4: Replay Consequence Frontier

solver replay はまだ太いが、var-var consequence を単純に捨てると public 型が壊れる。
routing graph は propagation を証明できても、generalization / public projection が
materialized evidence を読んでいるためである。

根拠:

- `notes/design/2026-06-24-weighted-var-var-routing.md`
- `docs/infer-solver-invariants.md`

順番:

1. `YULANG_REPLAY_EVIDENCE_ONLY_SKIP=1` prototype を測定専用として維持する。
2. evidence-only bounds を正式な solver data として分離する。
   - normal bounds: immediate replay / events / probing
   - evidence-only bounds: compact / generalization / future replay scan
3. generalization と public projection が evidence-only bounds を通常 evidence と同等に読むことを明示する。
4. public canary で `apply` / `compose` / parser choice / nested handler residual を固定する。
5. bounded online search 依存を減らし、cheap positive route cache か per-pivot frontier へ寄せる。
6. env-gated で smoke が安定してから、var-var replay だけ production path へ切り替える。

やらないこと:

- unweighted reachability を skip 条件にしない。
- weighted SCC を型変数等式として collapse しない。
- row-tail / terminal / constructor bounds を最初から routing graph に入れない。
- `seen` を消さない。

成功条件:

- `constraint.replay_accepted` が大きく下がる。
- `constraint.drain` が下がる。
- public latent effect が消えない。
- internal tests が「normal bound materialization」を仮定しているだけなら、テスト側で分類して残す。

## Phase 5: Direct-Style / Pure Island

ここは後回し。

pure code まで generic handler VM で動かすのは意味論上不可避ではないが、今すぐ触ると
runtime / inference / monomorphize の境界を同時に揺らす。

着手条件:

- compiled-unit cache が entry-only edit で効いている。
- runtime scope state が marker-heavy workload に効いている。
- release gate が一コマンドで回る。

方向:

- effect-free region を direct-style SSA / register VM へ落とす。
- control region だけ CPS / handler VM に残す。
- generic effect dispatch は動的 handler 境界だけで払う。

native backend はこの後に戻す。native を急ぐと、今の実装由来コストと backend 設計問題が混ざる。

## Suggested Order

短期:

1. compiled-unit cache Phase 2: namespace surface
2. generalize restart summary metrics

中期:

5. typed/runtime compiled-unit surface
6. wasm / playground std bundle import
7. generalize root cache
8. runtime ScopeState shadow

長期:

9. ScopeState production path
10. evidence-only replay frontier production path
11. direct-style / pure island
12. native backend revisit

## What To Do Next

最初の運用タスクは、`scripts/performance-gate.sh` を full mode で回して
current HEAD の baseline を保存すること。

理由:

- cache / generalize / runtime / replay のどれを触っても同じ gate で比較できる。
- WSL2 の stack overflow / hang を timeout で封じ込められる。
- 「速くなったが public type が壊れた」を防げる。

次点は compiled-unit cache の `CompiledUnitManifest + CompiledSyntaxSurface`。
これは高速化としても効くが、release / playground / user dependency cache の基盤でもある。
