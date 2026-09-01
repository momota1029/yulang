# Gate 10 public production-companion measurement

Date: 2026-09-01
Status: completed, candidate-only evidence
Authority: declaration-companion addendum Gate 10 and the Gate 2 performance
amendment §6 deferred-production-companion measurement.

## Scope and identity

This measures the public direct-CST path for a braced Struct companion:

```text
struct S {} with { my value = value }
```

The one-declaration form is functionally covered by
`gate10_declaration_companion_public_scope_matrix` through AST,
`parse_file`, and direct-root paths before this measurement.

| field | value |
| --- | --- |
| branch base / candidate source base | `13e2a5b818d7611dcf20f22bf60304ab49781585` |
| historical unrun pre-public baseline | `b2df4dab` (Gate 5 isolated handoffs; no semantically equivalent public companion route) |
| candidate code patch SHA-256 | `dd0233a2f97750853c958f631698b283d1bd757775afa7bffe246efe71d91387` |
| candidate test blob | `5561548a22b1216354ee367c913d9b84aea6fe68` |
| candidate harness blob | `45be7485b456146eb58ea0ae7754813ed1d22a2c` |
| marker-delimited harness SHA-256 | `45e3f3032dfbfc9b1b5ca35f115889a4ca992f083ee5e947cd7a6062be9ef639` |
| prebuilt binary | `target/debug/deps/yu_syntax-67577d316539ca9e` |
| binary SHA-256 | `07f82d96c8fed9116c0255f57df0541e08ca40d161dd3883d6ab81124a0657e6` |
| toolchain | `rustc 1.98.0 (88d9e12ae 2026-08-18)`; `cargo 1.98.0 (797e8a9bc 2026-08-05)` |
| build profile | default test profile, locked/default features, `CARGO_INCREMENTAL=0 RUSTFLAGS=''` |
| build command, excluded from samples | `env CARGO_INCREMENTAL=0 RUSTFLAGS='' cargo test -p yu-syntax --locked --no-run` |
| CPU | CPU 10, pinned with `taskset -c 10`; allowed affinity was 0–11 |

The candidate code patch is intentionally limited to the final public matrix
and this ignored harness; production companion owner wiring is already in the
base commit.  The baseline is named only for provenance and was not run: it
cannot parse the same public declaration-companion grammar, so no percentage
or baseline/candidate regression claim is valid.

## Harness and work ledger

The ignored harness at
`crates/yu-syntax/src/lib.rs`, between the named Gate 10 markers:

- constructs a 379,999-byte source (10,000 declarations), header, and empty
  syntax environment before the timed interval;
- measures exactly eight public `parse_file` invocations with `Instant`;
- retains and black-boxes the final `ParsedFile`;
- only after the interval validates losslessness, no diagnostics/recovery, and
  exactly 10,000 `StructDeclaration` / `DeclarationCompanion` nodes;
- emits one `GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS=<decimal>`
  marker after validation.  The libtest prefix shares that line, so extraction
  uses the unique marker substring rather than a line-start anchor.

Per `parse_file`, the public root loop processes 10,000 declarations.  Each
Struct reaches two bounded eligible-tail handoff probes (Header rejects at
`{`; actual-close trailing accepts `with`), then one direct streamed braced
companion with one canonical binding item.  This is O(D), with 20,000
eligible-tail probes per parse and 160,000 across the eight-repeat kernel.  No
probe is added to the protected canonical Statement sequence loop; no direct
AST item vector, replay, cache, side index, or CST rescan occurs.

The interval necessarily includes public-entrypoint `Arc` clones,
replacement/drop of the retained `ParsedFile`, and `black_box`.  Public
`parse_file` also rebuilds its empty operator table and materializes
diagnostics once per repeat.  These are recorded as public-route work, not
removed as harness contamination.  Companion brace scopes also record O(D)
rollback-stack undo entries (about six per declaration) until a full parse
ends; peak RSS therefore includes normal CST plus that real public parser
allocation.  The direct path does not construct the AST companion result
`Vec`.

## Protocol

The direct binary was first checked with:

```text
taskset -c 10 target/debug/deps/yu_syntax-67577d316539ca9e --list
```

which found exactly
`tests::gate10_public_production_companion_performance_harness: test`.
Before every invocation, the process list was checked for `cargo`, `rustc`,
and `yu_syntax-` test contention.  Each valid run used:

```text
timeout --foreground 110s taskset -c 10 /usr/bin/time -v -o <sample>.time \
  target/debug/deps/yu_syntax-67577d316539ca9e \
  --exact tests::gate10_public_production_companion_performance_harness \
  --ignored --nocapture --test-threads=1
```

Stdout, stderr, and `time -v` output are preserved in the paired
[raw artifact](2026-09-01-gate10-public-companion-raw.md).  `--nocapture`
is required to retain the passing harness marker.  Marker values measure only
the eight-parse interval; `time -v` wall/RSS cover the whole process,
including setup, validation, libtest, and teardown.

Two launches were invalid and excluded from kernel statistics but counted:

1. During the first attempted warm-up, concurrent prebuild `cargo`/`rustc`
   activity was observed; the in-flight launch was interrupted after 40.38 s.
   It used the prebuild-era `yu_syntax-bcf5c27414ab47ba` binary, emitted no
   kernel marker, and is invalid/excluded from candidate statistics while still
   counted against the aggregate process/time budget.
2. A clean 10k×8 warm-up exceeded the initially proposed 60 s timeout
   (exit 124; 61.40 s wall, 18,208 KiB RSS; no marker).

After performance re-adjudication, one fresh warm-up and three candidate-only
measurements used the 110 s per-process cap.  No replacement samples were
used.  The six attempted processes consumed 459.18 s of process wall time,
under the 8-process / 10-minute Gate 10 budget; the final fresh sequence used
four processes.

## Results

The warm-up is excluded from medians and ranges.

| invocation | kernel seconds | whole wall seconds | peak RSS KiB | exit |
| --- | ---: | ---: | ---: | ---: |
| warm-up | 81.566441980 | 84.37 | 24356 | 0 |
| measured 1 | 84.642035955 | 88.75 | 24484 | 0 |
| measured 2 | 89.266634450 | 93.42 | 24356 | 0 |
| measured 3 | 86.740094588 | 90.86 | 24484 | 0 |
| measured median | 86.740094588 | 90.86 | 24484 | — |
| measured range | 84.642035955–89.266634450 | 88.75–93.42 | 24356–24484 | — |

All four fresh-process preflights were clear; each exited 0, was CPU-pinned,
and emitted exactly one marker.  Every accepted run validated the same
diagnostic-free, lossless 10,000-Struct/10,000-companion output.

## Conclusion and residual uncertainty

This is bounded, candidate-only public-route evidence.  It establishes that
the final public Struct braced companion path completes its 80,000-parse
kernel on the recorded environment with the stated wall/RSS envelope.  It
does not establish an improvement, regression percentage, or zero-cost claim:
there is no semantically equivalent pre-public baseline, and whole-process
RSS includes public parser/CST allocation and post-kernel setup/validation.
The static ledger accounts for the declaration-tail probe and rollback-stack
work; no ordinary canonical Statement hot-loop work was added by this Gate 10
test/harness diff.
