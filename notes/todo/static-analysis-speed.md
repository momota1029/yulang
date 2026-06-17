# Static Analysis Speed TODO

目的: playground と scripting の遅延を低く保つ。ただし、根本的な compile-time cost を
場当たり的な cache の裏に隠さない。

設計参照:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`

## 現在の checkpoint

- principal-unify は default monomorphize route。
- specialization body rewrite は queue 化され、target ごとに profile される。
- block rewrite は redundant pre-walk を避け、`showcase` の monomorphize time を減らす。
- compiled-unit artifacts は syntax / namespace / typed / runtime surfaces を持つ。
- wasm は std compiled-unit artifacts を embed し、source std を fallback として使う。

## 主な risk

- debug evidence が hot export paths に戻ってくる。
- runtime fallback が missing principal evidence を隠す。
- cached std work が file-SCC artifact system ではなく std 専用特例になる。
- syntax / operator exports が manifest に入らないと cache validation が弱くなる。

## TODO

- 2026-06-17 performance review で挙がった候補を、まず計測仮説として扱う。
  - P0:
    - source/lower/cache: std/source lowering と file collection/cache 粒度。
    - specialize2 solver: root / instance ごとの solver 初期化、slot / role demand 反復。
    - control VM clone: `Expr` / `CapturedEnv` / continuation / marker frame。
    - effect continuation: request guard、active marker、resume continuation allocation。
  - P1:
    - record / polyvariant candidate merge の wide shape。
    - role impl / typeclass method resolution の candidate scan。
    - cast lookup の全走査。
    - pattern matching の recursive clone と `remove(0)` 系。
    - record field projection の線形探索。
    - ref update / composite value traversal の clone。
    - source dependency SCC cache の coarse granularity。
  - P2:
    - Rowan / editor token traversal。
    - path / symbol / type constructor / effect path / role key intern 化。
- 計測を追加するなら、まず次の counter / timing を見る。
  - source collection: file count、module load discovery time、`sources::load` time。
  - infer/lower: lowering time、resolve time、body lowering count、diagnostic evidence count。
  - specialize2: solver count、slot count、slot solve loop count、role demand iteration count、
    cast lookup count、typeclass candidate scan count、instance key count。
  - runtime/control: VM compile time、VM eval time、`Expr` clone 回数、captured env clone 回数、
    continuation allocation count、marker frame scan count。
  - surface/editor: parse tree construction time、semantic token traversal time、wasm warm/cold time。
- 最初の benchmark slice は、既存 script を timeout 付きで動かして baseline を保存する。
  - `bench/static_analysis_bench.sh --repeat 5`
  - `bench/static_analysis_bench.sh --repeat 5 --infer-only`
  - WSL2 では必ず外側に `timeout` を付ける。
- 2026-06-17 baseline:
  - public examples の `check` は total 342〜442ms 程度。
  - `collect+load` は 70〜85ms 程度で、source collection/load は見えているが最大ではない。
  - `infer` は 270〜350ms 程度で、今の public example baseline では最太。
  - `--no-cache run --print-roots` wall clock は `showcase` だけ 1.16〜1.25s、他は 0.43〜0.53s。
  - 次は infer 内訳と showcase run の build/specialize/control VM 内訳を切る。
- 2026-06-17 timing refresh:
  - `bench/static_analysis_bench.sh` は check timing、lowering 内訳、runtime phase timing、control VM stats を出す。
  - public examples の static check では `lower.drain` と `lower.resolve` が 100ms 前後で太い。
  - `showcase` run は `build_poly` 330〜420ms、`specialize` 20〜30ms、`control_lower` sub-ms、VM eval が最大。
  - COW env 前の `showcase` VM eval は約 0.67〜0.70s。
  - `eval_expr` の丸ごと `Expr` clone を外すと `expr_clones` は 0 になるが、VM eval の改善は小さめ。
  - `CapturedEnv` を `Rc<HashMap>` + copy-on-write にすると、`showcase` VM eval は約 0.39〜0.48s まで落ちる。
  - 残りの runtime 側は `apply_value` 90247 回、`force_thunk` 23126 回、handler continuation 2456 回が次の観測点。
- 2026-06-17 effect path intern experiment:
  - `showcase` では path prefix check 118496 回、prefix segment 比較 418073 回、
    path equality check 6689 回、equality segment 比較 26521 回。
  - control VM runtime 内部は effect path を `InternedPath` にし、request/marker/handler 比較を segment id 列にした。
  - VM eval は 0.40〜0.42s 付近で、COW env ほどの勝ちはない。次に runtime を触るなら、
    path intern より active marker scan / continuation resume / apply-force chain を見る。
- 2026-06-17 record-field fallback batch:
  - `YULANG_ANALYSIS_TIMING=1` では `std.control.var.ref.update` の compact merge と
    unresolved selection fallback が太く、path lookup より analysis/merge 側が支配的に見える。
  - record-field fallback は selection target が一括で決まるのに、各 selection ごとに
    constraint drain していたため、fallback batch では record-field constraints をまとめて流すようにした。
  - `showcase` infer-only latest sample は total 0.407〜0.421s、infer 0.325〜0.338s 付近。
    効果は小さく、次は compact merge の var-only interval cross product と method-tainted role pass の
    再走査を切る方がよさそう。
- 2026-06-17 infer analysis timing split:
  - `check` の `timing:` に `analysis.route/work/role/taint/role_solve/quantify/instantiate/record_field`
    と quantification subphase を追加した。
  - `showcase` latest repeat 3 sample では `analysis.quantify` が 0.131〜0.137s、うち
    `analysis.quantify_generalize` が 0.117〜0.123s。`analysis.instantiate` は 0.046〜0.047s、
    `analysis.role_solve` は 0.025〜0.028s。
  - 次は `generalize_root_with_prepasses` の compact / merge / role prepass 内訳を切る。
- 2026-06-17 infer generalize / constraint drain timing split:
  - `generalize_root_with_prepasses` は `generalize_apply_merge` 0.025〜0.026s、
    `generalize_resolve_roles` 0.025〜0.026s、`generalize_compact` 0.016〜0.017s、
    `generalize_collect_dominance` 0.013s 前後。
  - `instantiate_subtype_predicate` は 0.043〜0.046s で、instantiate の大半を占める。
  - `constraint.drain` は 0.098〜0.103s、drain 18118 回、work 42159 件、subtype call 17584 回。
    `constraint.max_initial_queue` は 2 なので、小さい即時 drain を大量に叩く形が見えている。
  - ただし、単純な batching は今のところ外れ。contiguous `InstantiateUse` をまとめる実験は
    drain 回数こそ少し減ったが、max queue / work が太って infer が悪化した。
  - compact merge の invariant-neu constraints をまとめて流す実験も、queue が太って
    `constraint.drain` と infer が悪化した。
  - 次は単純な drain batching ではなく、instantiate predicate の生成/replay 削減と、
    generalize merge/role resolve loop の再 compact 削減を候補にする。
- typed-surface import の role / impl / effect fidelity を広げる。
- compiled-unit manifest validation を厳しくする。
- persistent cache を user dependency SCCs に一般化する。
- source dependency SCCs を長期的な cache unit として保つ。
- realm/band を cache key と dependency identity に入れる。
  - `notes/design/source-realm-band-plan.md` を実装単位へ分解する。
  - realm/band が std 専用 cache 特例にならないよう、source graph の責務として扱う。
- benchmark scripts と phase timings を最新に保つ。
- first-run と warmed-run の playground timings を分けて見る。
- intern 化は候補を測ってから入れる。
  - module path / source path / symbol name / type constructor / effect path / role key を候補にする。
  - full `Type` key の正規化差分で instance cache が割れていないか見る。
- Rowan cost は疑いとして扱い、置き換え前に測る。
  - parse tree construction
  - token traversal
  - editor colorize
  - wasm warm path
  - LSP incremental update
- compile-time regression を次で追う。
  - infer / lower
  - core export
  - runtime lowering
  - monomorphize
  - VM compile
  - VM eval

## 原則

- runtime rediscovery より one-pass exported evidence を優先する。
- execution に不要な diagnostic / debug evidence は opt-in に保つ。
- process-local cache は最終 architecture ではなく oracle として扱う。
- 広い refactor の前に測る。
- ownership と merge semantics が明確でない parallel static-analysis pass は入れない。
- 「Rowan が重いはず」から始めず、phase timing と allocation/counter で原因を切る。
