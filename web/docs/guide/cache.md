# Cache

Yulang caches compiler artifacts. It does not cache program output: every run
still executes the program after the compiler has found or rebuilt the needed
artifacts.

## Artifact types

| Artifact | What it stores | When it helps |
| --- | --- | --- |
| `.yuunit` | compiled syntax, namespace, typed, and runtime surfaces | Reusing standard library or unchanged dependency modules |
| `.yuir` | inferred principal poly IR | Re-running the exact same source set without inference |
| `.yuvm` | lowered control-VM program | Re-running the exact same source set without specialization or VM lowering |

The important incremental artifact is `.yuunit`. A cached `.yuunit` can be
imported as a prefix, then Yulang compiles only the source files that are not
covered by that prefix.

## Route labels

Pass `--runtime-phase-timings` to see which route was used:

```sh
yulang run --runtime-phase-timings path/to/file.yu
```

`run.cache` may report:

| Route | Meaning |
| --- | --- |
| `control-hit` | Exact `.yuvm` hit |
| `poly-hit` | Exact `.yuir` hit |
| `compiled-unit-hit` | Exact full-source `.yuunit` hit |
| `std-prefix-hit` | Cached standard-library `.yuunit` was reused |
| `std-prefix-build` | The standard-library prefix was built and then reused |
| `source-unit-prefix-hit` | One cached dependency prefix was reused |
| `merged-source-unit-prefix-hit` | Several independent cached prefixes were merged and reused |
| `full-miss` | Fresh compile from source |

For local editing, `std-prefix-hit`, `source-unit-prefix-hit`, and
`merged-source-unit-prefix-hit` are the interesting cases. They mean the
compiler skipped unchanged prefix code and compiled only the remaining suffix.

## Cache commands

```sh
yulang cache path
yulang cache stats
yulang cache clear
```

Use `--no-cache` on a single command to bypass cache reads and writes:

```sh
yulang run --no-cache path/to/file.yu
```

Invalid or old cache entries are not language errors. Yulang skips them and
falls back to compiling from source.

## Current limits

The cache is conservative. It speeds up repeated runs and local edit cycles,
but clean builds still pay the full parser, lowering, inference, and runtime
lowering cost.

The package-level `realm.toml` / `yulang.lock` workflow is still experimental.
Future realm and band identities should make dependency cache keys more precise.
