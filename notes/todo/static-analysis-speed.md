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

- typed-surface import の role / impl / effect fidelity を広げる。
- compiled-unit manifest validation を厳しくする。
- persistent cache を user dependency SCCs に一般化する。
- source dependency SCCs を長期的な cache unit として保つ。
- benchmark scripts と phase timings を最新に保つ。
- first-run と warmed-run の playground timings を分けて見る。
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
