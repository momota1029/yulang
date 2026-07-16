# Solver Invariants

この文書は、Yulang の型推論 solver を今後触るときに守る不変量を整理する。
実装の完全な証明ではなく、2026-06-23 の `ref.update` ハング修正で確認した
「壊すと再び無限 replay や private evidence leak が起きる契約」を固定するための文書である。

主な根拠は次のファイルに置く。

- `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`
- `spec/2026-05-31-effect-variable-subtractable.md`
- `notes/design/2026-06-22-directed-stack-weight-implementation.md`
- `notes/diagnostics/2026-06-23-ref_update.md`

## Public Type Boundary

public scheme は、ユーザーが書ける型と、公開してよい effect row だけを表示する境界である。
solver の内部 evidence は保持してよいが、public type surface へ漏らしてはいけない。

public scheme に出してはいけないもの:

- stack id 表示としての `#...`
- `AllExcept(...)` / `AllExceptMany(...)` を持つ hidden stack evidence
- private data-position tail
- method body 内だけで必要な local wildcard boundary
- unresolved placeholder を隠すための `Any`

`Any` は Top 型、`Never` は Bottom 型、`Unknown` は唯一の不明型である。
public boundary の cleanup や fallback で `Any` / `Never` を placeholder として使ってはいけない。

実装上の主な場所:

- `crates/infer/src/generalize/*`
- `crates/infer/src/generalize/finalize.rs`
- `crates/poly/src/dump/*`
- `crates/yulang/src/source/format.rs`

## Stack Evidence Visibility

stack evidence は、handler hygiene と residual subtraction を支える内部証拠である。
内部 graph では `PWeight` / `NWeight` / `filter` を使ってよい。
ただし surface 型では、ordinary effect row として説明できる residual だけに射影する。

特に `ref.update` のような data-position effectful function では、field 内部の返り effect tail に
private stack evidence を持たせる。public tail そのものを field row の item として混ぜると、
payload / thunk / function boundary が marker を作る差分を失い、runtime 側の hygiene が壊れる。

現在の対応は次の形である。

```text
field row internal: [ref_update a; PWeight(@ref[AllExcept(ref_update _)], kappa)]
projection:         kappa <: e
public surface:     ref(e & b, a) -> (a -> [b] a) -> [e, b] unit
```

ここで `kappa <: e` は ordinary residual を public tail へ戻す projection であり、
`kappa = e` という型等式ではない。

実装上の主な場所:

- `crates/infer/src/lowering/signature_effect.rs`
- `crates/infer/src/lowering/expr/method_body.rs`
- `crates/infer/src/annotation/constraints.rs`

## Row-Tail Polarity

row split は directed stack weight の契約に従う。
左重みと右重みを row split の前に単一の `StackWeight` へ潰してはいけない。

weighted row upper bound は次の形として扱う。

```text
alpha @ L <: [K; beta]
```

消費できる head は次だけである。

```text
J = K intersection Common(L)
```

split は次の形になる。

```text
alpha <: [J; gamma]
gamma @ (L minus J) <: beta
```

`J` が空なら residual tail を作らず、tail 側へ進める。
right pop は row head の消費判定へ参加しない。variance に沿って target tail へ分配する。

残差 key は `(source, J, L minus J)` であり、target tail を含めない。
target tail を含めると同じ split を共有できず、row cycle の燃料になる。

実装上の主な場所:

- `crates/infer/src/constraints/row_effect.rs`
- `crates/infer/src/constraints/directed_weight.rs`
- `crates/infer/src/constraints/mod.rs`

## Replay Termination

bound replay は、W-Mix 後の exact label を使う。
`compose_for_replay()` で `pop(n)` を `pop(1)` へ丸めてはいけない。
それは型重みの等式ではなく、以前の実装が停止性を見た目だけで支えていた clamp である。

replay の停止性は、次を組み合わせて支える。

- self-tail split は finite colored observation では no-op とする。
- residual tail は `(source, J, L minus J)` で hash-cons する。
- var-var replay は通常の `SubtypeConstraint { lower, upper, weights }` 経路を通す。
- bounds table へ保存する直前に、同一 endpoint / 同一 static boundary の alias cycle を subsume する。

same-boundary alias-cycle subsumption は worklist / bounds-table の保存規則である。
surface type の簡約規則でも、`pop(n) = pop(1)` という型等式でもない。

実装上の主な場所:

- `crates/infer/src/constraints/mod.rs`
- `crates/infer/src/constraints/machine/bounds.rs`
- `crates/infer/src/constraints/tests/case_01.rs`

## Handler Hygiene

handler は、自分が処理する effect だけを処理する。
callback や data field 由来の residual を、たまたま内側にある handler が奪ってはいけない。

重要な境界:

- callback return effect は `take(Empty)` 相当で protect され、内側 handler へ勝手に消費されない。
- `loop(x: [_] _)` のような local wildcard handler は内部 evidence を持つが、outer public scheme へ stack id として輸出しない。
- method result annotation は method body lowering 中の raw body effect へ直接接続せず、receiver / args を含む method scheme の結果位置で check する。
- data-position effectful function の tail は private tail に lower し、ordinary residual だけを public tail へ戻す。

`ref.update` はこの契約の canary である。
`r.update_effect()` の `ref_update` は local handler が処理するが、callback `f v` の effect は local handler に奪われず、method の residual へ残る。

## Owner-Level Dirty Scheduling

owner-level dirty scheduling は、forced method-role pass 内で terminal owner の再実行を省くための
内部最適化である。scheduling unit は厳密に `SelectionUse.parent` とする。cached terminal record を
clean とみなして skip してよいのは、前回の solve が観測したすべての可変 resource が不変であり、
それ以後の関連 mutation がすべて欠落なく反映されている場合だけである。再利用時にも record は
現在の unresolved-selection membership に対応していなければならない。owner の順序は deterministic
なまま保ち、一つの forced pass で同じ owner を二度実行しない。

cache / replay してよい outcome は `RootUnavailable` と `NoProgress` だけである。`Progress` は cache
にも replay にも入れない。false dirty は実行時間を失うだけだが、false clean は実際の role resolution
を抑止する correctness bug になる。この非対称性を review の重みにも反映し、clean 判定側を強く疑う。

owner solve の結果へ影響しうる可変 resource は、
`crates/infer/src/constraints/mutation.rs` にある current typed vocabulary で表す。このファイルを live な
一覧の source of truth とし、別の文書へ variant 一覧を複製しない。すべての effective observable
mutation は、authoritative mutator で対応する typed key または `InvalidateAll` を emit する。
authoritative な executable inventory は
`crates/infer/src/analysis/session/dirty_scheduling_contract.rs` の 25 行 mutation-contract matrix であり、
表をこの文書へ複製しない。

typed enum と test matrix が存在するだけでは coverage にならない。production owner solve は、
`#[cfg(test)]` に閉じない production-reachable path を通して実際の read を記録する。Stage 5 の最初の
attempt は production scheduler に対して constraint read hook だけを test-gated のまま残し、この
soundness gap を作った。二度目の attempt は observation chain 全体を production wiring へ接続して直した。
今後 compact / role solver / candidate / taint に新しい read を足すときは、次を一つの chain として揃える。

- typed dependency を追加する。
- production-reachable な recording path を追加する。
- authoritative mutator で mutation coverage を追加する。
- positive / negative / removal-replacement test を追加する。
- 該当する場合は independent shadow oracle の coverage を追加する。

この chain を閉じられない path では owner skip を無効のままにし、fail closed にする。未使用の hook を
定義しただけでは coverage とみなさない。

関係するすべての outbox は同時に active とし、同期状態を保つ。journal は各 owner の eligibility 判定前と、
solve 自身の新しい terminal record を publish する前に drain する。serial continuity と generation stamp を
検査し、journal の loss / truncation、overflow、audit disagreement、inactive-window drift、contract mismatch
のいずれかがあれば、変更前と同じ full owner pass へ倒す。先の owner が起こした mutation は同じ pass の
後続 owner を wake する。後続 owner が起こした mutation は、先に実行済みの owner を次の pass にだけ dirty
として残す。

subscription-aware emission は、共有 subscription set がすべての live terminal record の dependency key
の正確な union である場合だけ sound である。reverse subscription と mutation-outbox subscription は一緒に
更新し、record の publish は古い dependency set を atomically replace する。owner の remove / replace /
settle では subscription も外す。すべての effective mutation は subscription filter より先に coarse audit
generation を進め、journal entry を emit しない場合も例外にしない。既存 record の key は、その record へ
影響する後続 mutation より先に subscribe 済みでなければならない。mutation を filter してよいのは、現在
eligibility を持つ reusable record がその exact key に一つも依存しない場合だけである。ここで `unsubscribed` は
「この mutation を観測しうる reusable record がない」を意味し、「event listener がたまたまいない」を
意味しない。これは Stage 6 で確定した subscription-aware emission の前提である。

method taint は forced pass ごとに一度 rebuild し、deterministic に normalize して eligibility 判定前に
diff する。変化した queried entry は `MethodTaint` を emit し、その projection から到達する selection は
`Selection` dependency に含める。incremental method-taint はこの scheduler の範囲外である。

record と raw ID は session-local であり、serialize しない。owner が resolve する、settle / quantify される、
unresolved membership を失う、progress する、replace される、cap に達する、または session が終わるとき、
record と reverse edge を残さない。

既存の coarse whole-session guard は最初の fast path として残す。この guard の削除、または owner scheduler を
generalization / early fallback に使う拡張は別の design review を必要とし、cleanup として黙って混ぜない。

cap exhaustion は silent success にせず fail closed にする。per-owner dependency cap を超えた owner は
non-cacheable とする。cap category は owner count、per-owner dependency count、global dependency-key count、
reverse-edge count、journal-burst size、retained-byte budget である。このうち global cap の exhaustion は
reusable eligibility を clear / disable し、full owner loop へ戻す。現在の数値は
`crates/infer/src/analysis/session/owner_dirty_scheduler.rs` の `OwnerDirtySchedulerBudget::default` と同 module の
focused test を source of truth とし、この文書では固定しない。

independent exact-snapshot shadow oracle、always-solve control mode、mutation-contract matrix / harness、
representative fixture の semantic paired run は、歴史的 scaffolding ではなく継続的な assurance として残す。
いずれかを削除するには、redundancy を示す専用 review が必要である。一件でも false-clean counterexample が
見つかったら、影響 path の owner skip を無効にし、失敗例を regression test として保存し、欠けた dependency
または mutation を authoritative layer で直す。全 fixture set で mismatch が再び zero になるまで再有効化しない。
fixture / path / name 固有の特別扱いで直してはいけない。

early-fallback activation、intermediate generalization iteration reuse、owner より細かい stable per-demand
scheduling identity、incremental method-taint は明示的な deferred scope であり、この invariant に黙って
取り込まない。constraint-replay deduplication も 2026-07-16 に negative finding として調査を閉じている。
根拠は `notes/design/2026-07-16-constraint-replay-dedup-investigation.md` に置く。

実装上の主な場所:

- `crates/infer/src/constraints/mutation.rs`
- `crates/infer/src/analysis/session/owner_dirty_scheduler.rs`
- `crates/infer/src/analysis/session/dirty_scheduling_contract.rs`
- `notes/design/2026-07-15-owner-level-dirty-scheduling-spec.md`（historical design / provenance。maintained checklist ではない）

## Standard-Library Canaries

次の public signature は、solver 不変量の canary として扱う。
壊れたときは表示だけでなく、内部 evidence / row-tail polarity / replay termination のどれが崩れたかを見る。

- `std.control.var.ref.update`
  - public 型に `#...` / `AllExcept(...)` が出ない。
  - callback effect `b` と ref residual `e` が共起し、片方が消えない。
- `std.control.var.ref` の `update_effect` field
  - field 内部には private evidence が残ってよい。
  - public method surface へ private evidence を輸出しない。
- parser combinator / `choice`
  - parser effect の residual が handler boundary を越えて正しい tail に残る。
- `std.control.flow.for_in`
  - iterator callback の effect が loop handler に奪われない。
- `std.control.nondet.once` / `.list`
  - deep handler 型が shallow handler 型へ潰れない。

## Metrics Contract

hardening phase の metrics は「観測」だけに使う。
デフォルト出力を汚さず、最適化や探索打ち切りを同時に入れない。

見たいもの:

- slot count
- row variable count
- edge / bound count
- SCC count
- replay count
- max replay depth
- `solve_slots` / `generalize` / `compact` time
- role demand count

metrics で見えた重さは、別 commit で原因を説明してから直す。
timeout や clamp を、型推論の意味論として混ぜてはいけない。

2026-06-24 時点では、`check-poly` timing block に次の hardening metrics を出している。
これらは constraint machine / analysis coordinator で既に保持している情報の観測であり、
solver 最適化や replay 停止条件は変更しない。

- `infer.type_var_count`
- `infer.row_tail_var_count`
- `infer.type_node_count`
- `infer.pos_node_count`
- `infer.neg_node_count`
- `infer.neu_node_count`
- `constraint.edge_count`
- `constraint.replay_generated`
- `constraint.replay_enqueued`
- `constraint.replay_accepted`
- `constraint.replay_duplicate`
- `constraint.replay_trivial`
- `constraint.replay_prefiltered`
- `constraint.max_replay_inputs`
- `constraint.max_replay_generated`
- `constraint.max_replay_enqueued`
- `constraint.max_replay_accepted`
- `constraint.max_replay_duplicate`
- `constraint.max_replay_trivial`
- `constraint.max_replay_prefiltered`
- `constraint.max_replay_var_var`
- `analysis.scc_component_count`
- `analysis.quantify_max_component_defs`
- `analysis.quantify_generalize_roots_with_restarts`
- `analysis.quantify_generalize_max_iterations_per_root`
- `analysis.quantify_generalize_max_restarts_per_root`
- `analysis.role_demand_count`
- `analysis.role_resolve_demands`
- `analysis.role_resolve_candidate_scans`
- `analysis.role_resolve_candidate_matches`
- `analysis.role_resolve_prerequisite_candidate_scans`
- `analysis.role_resolve_candidate_cache_hits`
- `analysis.role_resolve_candidate_cache_misses`

`infer.row_tail_var_count` は row tail として観測された変数数であり、完全な row kinding ではない。
`constraint.replay_enqueued` は古い名前を保っているが、現在は replay action の生成数として読む。
実際に queue へ採用された数は `constraint.replay_accepted`、既に `seen` にあったものは
`constraint.replay_duplicate`、top/bottom/self などで即時 no-op になったものは
`constraint.replay_trivial` で見る。
`constraint.replay_prefiltered` は、bound replay の action snapshot に入る前に落とした
duplicate/trivial の数である。これは solver の意味論ではなく、同じ canonical subtype 判定を
action 生成前へ前倒しした観測兼最適化である。

`constraint.max_replay_*` は 1 bound 追加あたりの replay fan-out であり、再帰的な replay depth
そのものではない。depth 風の爆発を疑うときは、総量の `constraint.replay_generated` /
`constraint.replay_accepted` と、fan-out の `constraint.max_replay_generated` /
`constraint.max_replay_accepted`、前倒しで削った `constraint.max_replay_prefiltered` を合わせて見る。

## Test Obligations

public signature golden test は、見た目だけではなく次を守る。

- public 型に private stack evidence が漏れない。
- expected residual が消えない。
- effect row が shallow/deep handler の違いを保つ。
- 失敗時に、どの symbol の public line が壊れたか分かる。

2026-07-02 時点では、個別 golden に加えて次の gate を置いている。

- `tests/yulang/cases.toml` の `public-signature` cases:
  `ref.update`、`choice`、`for_in`、`nondet.once/list`、data-position effectful
  function canary を CLI manifest 経由で固定する。
- `dump_poly_public_contract_spine_modules_hide_private_stack_evidence`:
  `std.control.var.ref`、`std.control.flow.loop`、`std.control.nondet.nondet`、
  `std.text.parse` の public signature type 部分を全走査し、private stack
  evidence が型表示へ漏れていないことを見る。

期待値は現在の実装出力に合わせて書き換えない。
`α [undet; β] -> [β] α` のような residual は、principal surface の一部として扱う。

- owner dirty scheduler の independent exact-snapshot shadow oracle と always-solve control は parity を保ち、
  mutation-contract matrix / harness の全行が authoritative emission と一致し続けることを確認する。
- representative fixture では scheduled / always-solve の semantic paired run を継続し、結果の mismatch を
  zero のまま保つ。これは導入時だけの validation ではない。

## Open Questions

- private tail / private stack id が public scheme へ残ったことを検出する dedicated assert を generalize 境界に置くか。
- local helper wildcard evidence の close / projection を、data-position function tail と同じ名前で扱うか、別の境界として分けるか。
- same-boundary alias-cycle subsumption の停止性説明を、研究メモ側でどこまで formalize するか。
- stable playground と nightly playground を release tag / branch とどう対応させるか。
- 現行 test coverage に加え、non-`cfg(test)` wiring を通して scheduled / always-solve owner behavior を比較する、より強い production-wired end-to-end CI canary を置くか（未承認の deferred decision）。

## Do Not

- inference 中に path / module / function / fixture 名だけを見る分岐を足さない。
- `Any` を不明型や fallback として使わない。
- `Never` を placeholder として使わない。
- 共起分析や極性消去に rigid / protected variable set を足して止めない。
- `compose_for_replay()` で pop count を丸めない。
- same-boundary subsumption を型等式として説明しない。
- golden test の期待値を、実装の現在出力に合わせて弱くしない。
- solver metrics と solver 最適化を同じ変更で混ぜない。
- owner scheduler の cap exhaustion を silent success として扱わず、full owner loop へ fail closed にする。
- 新しい constraint-solver mutable read を `#[cfg(test)]` 専用 hook だけで production scheduler へ接続しない。
- 別の design review なしに owner-level dirty scheduling を early fallback / generalization へ拡張しない。
