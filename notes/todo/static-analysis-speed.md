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
