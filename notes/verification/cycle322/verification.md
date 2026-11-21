# Cycle 322 verification

Lean 4.35.0, base `6efb1eeca`. Scope: the 46 new source modules listed
[in modules.txt](modules.txt). The full project, Rust and the operational
solver were not run.

- [Focused Lake build](build.txt), `--wfail`, 1,072 jobs including existing
  dependencies, exit 0. Each exact new source independently checked with
  `lake env lean --trust=0 -DwarningAsError=true FILE`:
  [46 successful source checks](source-status.txt).
- [Six independent Lean audits](audit-status.txt), all exit 0, importing
  `Yulang.*` directly: [ordinary existing readback](Cycle322Existing.txt),
  [fixtures](Cycle322Fixtures.txt), [source emission](Cycle322Emission.txt),
  [whole emission erasure](Cycle322Erasure.txt), [normalization/aliases](Cycle322Normalized.txt),
  [full ordinary producer](Cycle322Producer.txt).
- [Scoped unchanged gate body](scoped-gate.txt), 61,327 total declarations,
  exit 0; standard axioms only. Supplemental
  [transitive type/value dependency check](declarative-dependencies.txt):
  667 C322 declarations, 4,640 dependencies, no requested solver,
  physical-address, old-state or execution dependencies.
- `bash tools/verify-lean.sh . 6efb1eeca --no-build` [exit marker](diff-status.txt).
  Full output split at line ends:
  [00](diff-00.txt) [01](diff-01.txt) [02](diff-02.txt) [03](diff-03.txt)
  [04](diff-04.txt) [05](diff-05.txt) [06](diff-06.txt) [07](diff-07.txt).
  I-53: all 46 new modules have same-change barrel imports.
- Additional exact [source readback proof](exact-source-readback.lean) and
  [standalone trust=0 output](exact-source-readback.txt): the old real emitter
  produces role 2, endpoints [(3,3)], and named request (1,5); the lifted
  emitter and deterministic actual capture retain that exact request.
  Alias output target 12 is an equivalent presentation only when the
  original ordinary equations hold, not a new literal source emit.
