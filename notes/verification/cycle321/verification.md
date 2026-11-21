# Cycle 321 checks

Toolchain: Lean 4.35.0. Local C320 base `ce012694c`. Verification ran the
scoped clauses below, not the whole project, the operational solver, or Rust.

- Focused `lake build <52 modules in modules.txt> --wfail`:
  [full output](build.txt), 1,040 jobs with dependencies, exit 0.
- Each exact new source was separately checked by
  `lake env lean --trust=0 -DwarningAsError=true FILE`:
  [52 status lines plus any output](source-status.txt), all exit 0.
- Five standalone I-51 audits import built `Yulang.*` modules but no other
  audit files or bases. [Command statuses](audit-status.txt), all exit 0;
  [support](Cycle321Support.txt), [compiler](Cycle321Compiler.txt),
  [construction](Cycle321Construction.txt), [boundaries](Cycle321Edges.txt),
  [covariant](Cycle321Covariant.txt). Only standard axioms shown.
- The unchanged verification gate body, used with only the scoped C321
  imports, [passed](scoped-gate.txt) over 60,766 declarations. Not a
  complete import-barrel audit.
- Supplemental dependency walk over type/value references:
  [958 C321 constants, 5,106 dependencies](declarative-dependencies.txt).
  No references with the prohibited solver, old state, journal, slot,
  reobservation, executable resolver, or physical placement prefixes.
  Graph syntax and generic Lean proof machinery are not a solver.
- `bash tools/verify-lean.sh . ce012694c --no-build`:
  [status](diff-status.txt), full output split into
  [00](diff-00.txt) [01](diff-01.txt) [02](diff-02.txt) [03](diff-03.txt)
  [04](diff-04.txt) [05](diff-05.txt) [06](diff-06.txt) [07](diff-07.txt).
  The production Lean diff is append-only relative to the cycle start,
  outside new modules; I-53 imports are included. The top-level audit
  paths created temporarily during this cycle were migrated to
  `lean/Audit/`; no earlier-cycle paths were removed.
- Extra independent source/label smoke check, with protected name 55:
  [proof](fresh-shapes.lean), [output](fresh-shapes.txt), exit 0.
  The real clause compiler emitted exactly 56/57/58 as the where argument
  (lower/actual/upper), and 59 as the named associated output target.
  The concrete original model extends with all four equations, preserving
  the protected name. This does not assert the child resolves.
