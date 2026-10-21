# R249 — pinned standard-library source and imported syntax

Status: RESULT; source packaging and parser integration complete. R149 remains
OPEN. This result is not independent proof or review.

## Outcome

The exact 40-file standard-library closure listed in the R149 rev10 contract is
now bundled in `tools/inference-playground/pinned_stdlib.bin`. Each record
contains its repository-relative source path, original Git blob ID, and bytes.
The loader maps a module path such as `std::core::ops` to that exact source.
The implicit root `std` is also addressable as `lib/std.yu`.
Bundle SHA-256: `9eb726f179fa407122f1c31f4cd4cf98484bce3052d2486d7d7be84d4ec22b66`.

The playground now scans the bundled `std::core::ops` source and builds its
imported syntax environment from the source header. The environment carries
the `lib/std/core/ops.yu` dependency provenance and a fingerprint derived from
the pinned blob ID. No operator declaration is fabricated by spelling.

## Evidence

- The ordinary unit test recomputes Git's SHA-1 blob identity for every bundled
  file and checks all 40 identities against the bundle records.
- The module lookup test checks both the implicit root and `std::core::ops`
  source path and pinned blob ID.
- The unchanged 92-byte Console source parses with no syntax diagnostics using
  the imported environment; its recorded dependency is `lib/std/core/ops.yu`.
- Focused CLI tests for the six checked-in playground example files passed:
  identity (1), ordinary islands (6), diagnostics (1), repeated choice (1),
  and polymorphic closure (1).
- Running the exact R149 templates unchanged now advances Console beyond
  syntax parsing, but candidate inference returns `unsupported source`. Types
  still stops at `candidate lowering unavailable: StructuralProjection` for
  its tuple expression.

## Remaining work

This packet does not load imported semantic declarations into HIR, resolve
standard-library names, support tuples or role selection, execute whole
modules, handle authenticated host writes, publish Types/output, or close any
source/native proof gate. The next implementation seam is actual module and
semantic import resolution over these pinned bytes; the next Types source seam
is arbitrary finite tuple formation and inference. R149 and the broader user
goal remain open.
