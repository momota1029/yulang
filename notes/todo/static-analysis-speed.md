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

- 2026-06-23 hardening metrics inventory:
  - First baseline: `../benchmarks/2026-06-23-hardening-baseline.md`.
  - 既に `check-poly-std` / `check-poly-std-in` の出力には、analysis / constraint の観測点が入っている。
    これを hardening phase の solver baseline として使う。
    - phase time:
      - `analysis.route`
      - `analysis.route_scc_events`
      - `analysis.route_scc_quantify`
      - `analysis.route_scc_instantiate`
      - `analysis.work`
      - `analysis.role`
      - `analysis.role_solve`
      - `analysis.quantify`
      - `analysis.instantiate`
      - `constraint.drain`
    - solver work counters:
      - `constraint.drains`
      - `constraint.work_items`
      - `constraint.subtype_work_items`
      - `constraint.max_initial_queue`
      - `constraint.max_work_items`
      - `constraint.lower_bounds_added`
      - `constraint.upper_bounds_added`
      - `constraint.lower_replay_inputs`
      - `constraint.upper_replay_inputs`
      - `constraint.lower_replay_enqueued`
      - `constraint.upper_replay_enqueued`
      - `constraint.lower_replay_accepted`
      - `constraint.upper_replay_accepted`
      - `constraint.lower_replay_duplicate`
      - `constraint.upper_replay_duplicate`
      - `constraint.lower_replay_trivial`
      - `constraint.upper_replay_trivial`
      - `constraint.lower_replay_prefiltered`
      - `constraint.upper_replay_prefiltered`
      - `constraint.lower_replay_var_var`
      - `constraint.upper_replay_var_var`
    - SCC / role counters:
      - `analysis.scc_events`
      - `analysis.scc_merge_count`
      - `analysis.scc_merged_component_count`
      - `analysis.scc_reachability_*`
      - `analysis.scc_ready_*`
      - `analysis.role_passes`
      - `analysis.progressed_role_passes`
      - `analysis.generalize_*_constraints`
      - `analysis.instantiate_event_runs`
      - `analysis.instantiate_max_event_run`
    - compact / slot proxy:
      - `analysis.generalize_root_compact_nodes`
      - `analysis.generalize_root_compact_vars`
      - `analysis.generalize_component_unique_compact_vars`
      - `analysis.generalize_compact_iteration_nodes`
      - `analysis.generalize_compact_iteration_vars`
  - runtime / playground smoke 側は `--runtime-phase-timings` を使う。
    - `run.build_poly`
    - `run.specialize`
    - `run.control_lower`
    - `run.vm_eval`
    - `run.runtime_execute`
    - `run.effect_requests`
    - `run.request_resume_steps`
    - `run.marker_*`
    - `run.continuation_*`
  - すぐ使う baseline command:

    ```sh
    timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
    timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std-in examples/showcase.yu std.control.var.ref
    timeout 240s cargo run -q -p yulang -- --std-root lib --runtime-phase-timings --no-cache run --print-roots examples/showcase.yu
    timeout 300s bench/static_analysis_bench.sh --repeat 3 --infer-only examples/showcase.yu
    ```

  - 足りないもの:
    - named `slot_count` はまだ無い。現状は compact var count と constraint var/bound/replay count を proxy にする。
    - named `row_variable_count` はまだ無い。row variable だけを分けるなら `TypeArena` / constraint graph の structured count が必要。
    - named `edge_count` はまだ無い。現状は `constraint.lower_bounds_added` / `upper_bounds_added` と SCC edge counters を proxy にする。
    - recursive な max replay depth はまだ無い。現状は `constraint.max_replay_inputs` /
      `constraint.max_replay_generated` / `constraint.max_replay_accepted` を 1 bound 追加あたりの
      fan-out proxy として見る。
    - `solve_slots` という phase 名は現行 pipeline に直接対応しない。いまは `analysis.quantify_*` / `analysis.generalize_*` / `constraint.drain` に分けて読む。
  - 2026-06-23 に最初の code slice として、`check-poly` timing block に hardening metrics を追加した。
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
    - `analysis.role_resolve_candidate_scans`
    - `analysis.role_resolve_prerequisite_candidate_scans`
    - `analysis.role_resolve_candidate_cache_hits`
    - `analysis.role_resolve_candidate_cache_misses`
  - これは既存 constraint machine / analysis counter の観測だけであり、solver 最適化や replay 停止条件は変えていない。
    recursive な `max_replay_depth` と、tail 以外を含む完全な row variable kinding は次 slice に残す。
  - 2026-06-24 の replay fan-out slice で、1 bound 追加あたりの replay 最大値を追加した。
    `constraint.max_replay_inputs` / `constraint.max_replay_enqueued` /
    `constraint.max_replay_var_var` は、総 replay 数が太いときに局所 fan-out 由来かを切り分けるための
    観測点である。solver 最適化や replay 停止条件は変えていない。
  - 2026-06-24 の replay acceptance slice で、replay action の生成数と queue 採用数を分離した。
    `constraint.replay_generated` は `constraint.replay_enqueued` と同じ値を出す互換 alias で、
    実際に新規 work になったものは `constraint.replay_accepted`、`seen` に落ちたものは
    `constraint.replay_duplicate`、即時 no-op は `constraint.replay_trivial` として見る。
  - 2026-06-24 の replay prefilter slice で、canonical subtype 判定を replay action 生成前にも
    使うようにした。`constraint.replay_prefiltered` は、snapshot に入る前に落とした
    duplicate/trivial の数を表す。queue semantics は変えていない。
  - 2026-06-23 の次 slice で、role / typeclass method solve の candidate scan と
    compact candidate cache hit/miss を出すようにした。
    `analysis.work_apply_select_typeclass_method` と合わせて、候補走査が本命か、
    prerequisite / compact 再計算が本命かを切り分ける。
    同時に post-work SCC routing を `analysis.work_*` timing から外したため、
    showcase では `analysis.work_apply_select_typeclass_method` は 17.6ms 程度へ下がった。
    現時点の太い順は `analysis.route_scc_quantify` / `analysis.quantify_generalize`、
    `constraint.drain`、`analysis.role_solve`。
  - 2026-06-23 の quantify slice で、component サイズ分布と root ごとの
    generalize iteration / restart 最大値を追加した。
    これで `route_scc_quantify` が「大きい SCC」由来か、「小さい root の restart 反復」
    由来かを切り分ける。
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
- 2026-06-18 VM runtime counter split:
  - `RuntimeStats` と `bench/static_analysis_bench.sh` に、`apply_value` / `force_thunk` / primitive apply /
    continuation wrapper / marker frame の分岐別 counter を追加した。
  - `showcase` repeat 1 の初期観測では、VM eval 440ms 前後、`apply_value` 90247 回、`force_thunk` 23126 回。
  - 内訳では `apply_marked` 38784 回、`apply_closure` 32836 回、`force_marked` 10403 回、
    `force_expr` 7801 回、`force_effect` / `force_continuation` が 2456 / 1648 回。
  - continuation wrapper は `continue_with_request` 127268 回、marker frame は
    `marker_frame_calls` 117802 回、`marker_frame_request_closes` 64493 回、
    `marker_frame_resume_steps` 63554 回。次の runtime 本命は primitive apply ではなく
    request resume / marker frame wrapper の allocation と clone。
  - marker value view を frame 内で使い回す実験は、`showcase` repeat 3 で VM eval が 415〜462ms と揺れ、
    明確な改善ではなかったため棄却した。まずは wrapper 数そのものを減らす設計を探る。
- 2026-06-18 scalar marker fast path:
  - scalar value は effect request を発火しないので、marker frame の value close で marker list を作っても
    直後に捨てるだけだった。
  - `mark_value` の入口で scalar を返し、`close_marker_frame_result` は事前 `markers_for_value` をやめて
    `mark_value` 側の dedupe に一本化した。
  - `showcase` repeat 3 では VM eval が 380.4 / 371.5 / 379.1ms。次に見るなら、
    request resume wrapper 数を減らす continuation 表現側の設計変更。
- 2026-06-18 value continuation fast path:
  - `continue_with` / `continue_bind` は value / done 経路でも `Rc` continuation を作っていたため、
    Request 経路だけ `Rc` 化するようにした。
  - `showcase` repeat 5 では VM eval が 377.7 / 363.3 / 367.8 / 358.1 / 354.1ms。
  - `continue_bind_result` へ同じ変更を広げる実験は悪化寄りだったため棄却した。
    次は request resume wrapper 数を減らす表現変更か、pattern bind recursion の clone 側を見る。
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
- 2026-06-18 infer small optimization loop:
  - `instantiate_use` は scheme を事前 clone せず、`poly.defs` 上の scheme を直接 instantiate する。
  - `quantify_component` finalize は def parent map を component ごとに一回だけ作る。
    `showcase` の `q_fin` は 13ms 前後から 5ms 前後へ低下。
  - reachable role が空の prepass では compact clone と resolver call を避ける。効果は小さめ。
  - `Pos::Bot <: _` / `_ <: Neg::Top` は constraint enqueue 前に捨てる。
    `showcase` の `constraint.work_items` は 42159 から 37994 へ低下。
  - no-op / duplicate subtype constraint は public entry 側で empty drain しない。
    `showcase` の `constraint.drains` は 18118 から 15020 へ低下。
  - 次は `instantiate_subtype_predicate` の replay がどこで増えるかを、trivial edge ではなく
    bound replay / role predicate shape 側から見る。
- 2026-06-18 source collection module discovery skip:
  - collect/load の時間が似ていた原因は、ファイル二重 read ではなく module discovery の full parse と
    `sources::load` の full parse が重なっていたこと。
  - source text に `"mod"` が無いファイルでは module load discovery parse を skip する。
    `showcase` の `collect` は 39〜41ms から 8ms 前後へ低下。
  - `sources::load` の一時 subphase timing では、36 files の `load` 42.9ms のうち
    `full_parse` が 39.5ms。`header` 2.8ms、fixed point / table / module scan は sub-ms。
  - `read_header` keyword skip と module-load scan skip は改善が見えず棄却。
    まだ残る `load` 40ms 前後は parser / std source artifact cache 側を見る。
- 2026-06-18 embedded std loaded-prefix cache:
  - `sources::load_with_loaded_prefix(prefix, suffix)` を追加し、dependency-closed な loaded prefix を
    再利用して suffix だけ full parse できるようにした。
  - embedded full std / embedded playground std は thread-local loaded prefix cache を持ち、
    playground root source だけを suffix として parse する。
  - wasm playground の colorize と compact playground std run path はこの route を使う。
  - これは process-local の syntax/load cache であり、CLI の whole source-set artifact cache や
    将来の persistent source-SCC compiled-unit cacheとは別層。
  - 一時 benchmark（debug, same process）では embedded playground std の load-only が
    168.410ms/iter から 3.169ms/iter、build poly まで含めると 1169.368ms/iter から
    998.976ms/iter。parse/colorize warm path には大きく効き、build 全体では infer が残る。
  - 次の段は `LoadedFile` 再利用だけでなく、typed / runtime surface を import して
    unchanged dependency SCC の lowering / inference / runtime lowering を skip すること。
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
