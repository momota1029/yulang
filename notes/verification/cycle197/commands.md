# Cycle197 verification commands

Lean4.35.0, cached project dependencies. All commands run from lean/ unless stated.

- `lake build Yulang.GeneralNominalTraceRefreshExample197 --wfail` (checkpoint1143jobs).
- `lake build Yulang.GeneralNominalSyntaxExample197 --wfail` (checkpoint1148jobs).
- `lake build Yulang.GeneralNominalMixedExample197 --wfail` (final1150jobs).
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle197FinalGate.lean` (all195 declarations of11 new modules).
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle197PublicTypes.lean` (67 public theorem types).
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle197Mixed.lean` (mixed module axiom printouts).
- Intermediate strict gates and individual audit/build outputs are retained alongside this file; `.exit` files contain process exit codes.
- From repository root: `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`. PASS with8REVIEW flags; metaprogram axiom gates/axiom-printing audits are deliberately retained and independently executed. The initial run after owner ref advanced correctly rejected stale ancestry; merged latest1fd6a0d94 and reran successfully.

Gate permits only propext, Classical.choice and Quot.sound. No sorry/new axioms/native_decide added. Focused checks only: no full project build, historical audit sweep, hosted CI or runtime/Y2 execution. Source changes frozen before final checks; integration's additive files preserved but not independently full-built.
