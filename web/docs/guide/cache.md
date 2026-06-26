# Cache

Yulang caches compiler artifacts. It does not cache program output: every run
still executes the program after the compiler has found or rebuilt the needed
artifacts.

## Artifact types

| Artifact | What it stores | When it helps |
| --- | --- | --- |
| `.yucu` | compiled syntax, namespace, typed, and runtime surfaces | Reusing standard library or unchanged dependency modules |
| `.yuir` | inferred principal poly IR | Re-running the exact same source set without inference |
| `.yumo` | specialized mono IR | Re-running mono commands or rebuilding control VM from an unchanged source set |
| `.yuvm` | lowered control-VM program | Re-running the exact same source set without specialization or VM lowering |
| `.yures` | realm / band resolution target | Checking a source-site realm import against a cached target fingerprint |

The important incremental artifact is `.yucu`, short for "Yulang compiled
unit". A cached `.yucu` can be imported as a prefix, then Yulang compiles only
the source files that are not covered by that prefix.

`.yumo` is exact-source keyed. It is not a realm-wide mono cache: Yulang only
reuses it for the same source / resolution context.

`.yures` is a resolution record, not compiled code. For local
`realm/...::...` imports, a cached entry is accepted only if it still points at
the deterministic local `<realm>/<band>.yu` path and the source fingerprint
matches. Otherwise Yulang falls back to the filesystem resolver.

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
| `compiled-unit-hit` | Exact full-source `.yucu` hit |
| `std-prefix-hit` | Cached standard-library `.yucu` was reused |
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

`--no-cache` also bypasses checked realm-resolution cache lookups during source
collection.

## Current limits

The cache is conservative. It speeds up repeated runs and local edit cycles,
but clean builds still pay the full parser, lowering, inference, and runtime
lowering cost.

The package-level `realm.toml` / `yulang.lock` workflow is still experimental.
Future realm and band identities should make dependency cache keys more precise.
