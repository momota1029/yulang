# 2026-06-26 compiled-unit cache speedup

This note records the user-visible speedup from the compiled-unit cache work on
2026-06-26.

The important point is that the solver and runtime did not become
fundamentally cheaper in the clean-build path. The speedup comes from avoiding
work for source that has not changed:

- cached source-unit prefixes can be reused across entry edits;
- independent cached prefixes can be merged into one compiled-unit prefix;
- dependency-bearing non-root units are cached as dependency-closure artifacts;
- filesystem `std` can be imported as a compiled-unit prefix;
- wasm playground builds now embed compact and full std compiled-unit artifacts.

## Native std prefix measurement

Measured with the real `lib` std root and two separate entry files:

```text
--no-cache:        run.build_poly 2.914s, run.total 2.956s
std-prefix-build: run.build_poly 3.216s, run.total 3.258s
std-prefix-hit:   run.build_poly 215.2ms, run.total 256.0ms
```

The first cached run can be slower than `--no-cache`, because it writes both
the std prefix artifact and the full-source artifact. The payoff appears when
the next entry or local suffix keeps the same std root: the CLI imports the std
compiled-unit prefix instead of inferring std again.

## Source-unit cache gate

The latest source-metrics-only performance gate summary is:

```text
target/performance-gate/source-unit-materialize-check/summary.txt
```

The key source-unit smoke row reported:

```text
run.cache:
  merged-source-unit-prefix-hit
  compiled-unit-hit
  source-unit-prefix-hit
  compiled-unit-hit
```

This covers both cache routes:

- independent leaf modules reuse a merged source-unit prefix;
- a dependent module chain reuses a dependency-closure source-unit prefix.

## Playground effect

The wasm crate now embeds two build-time `.yucu` artifacts:

```text
embedded_playground_std.yucu  693861 bytes
embedded_full_std.yucu       1130242 bytes
```

The normal playground route first decodes the compact playground std artifact.
Parser/text-heavy examples that need more of std then fall back to the embedded
full std artifact. If either artifact fails validation, the old source route
remains available as a fallback.

This is why the playground speedup is visible: wasm no longer rebuilds the
compact/full std surfaces from source at runtime in the common routes.

## What this does not solve

The clean-build solver cost is still real. The latest gate still shows
`showcase-check-poly-std` spending hundreds of milliseconds in inference and
constraint draining:

```text
infer:             484.8ms
constraint.drain:  202.9ms
constraint.epoch:  147537
replay accepted:   62792
replay duplicate:  584369
```

So the next compiler-speed work should not be described as "make cache faster"
only. There are two separate tracks:

1. Reuse track:
   - external-reference table for dependency-bearing source-unit artifacts;
   - realm/band identity in cache keys;
   - stable release gate around cache route canaries.
2. Clean-build track:
   - root compact cache keyed by constraint/role epochs;
   - role view and dominance projection caching;
   - replay frontier work only after the current evidence invariants stay
     covered by tests.

For the current public/playground experience, the reuse track is the reason
the speedup is already visible.
