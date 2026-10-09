# Simple-sub legacy withdrawal checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Source baseline: `058f6f749106e3ceb523724e8c5c1634020ddd67`
Authority: [current explicit withdrawal policy](../design/2026-10-10-simple-sub-legacy-withdrawal.md)
Mode: M2; one bounded producer for code/tests, one disjoint ledger producer;
two independent reviews covering implementation/regression and dependency semantics.

## Actual dependency removal

The user's explicit withdrawal policy now also specifies per-mechanism
completion evidence: owner/callers, replacing Simple-sub operation, actual
dependency removal, focused regressions, exact retired proof edges/reasons and
remaining consumers. This policy clarification is M0, primary-owned, with no
reviewers or measurement processes. Scoped whitespace/reference checks suffice;
no compiler tests are rerun for this record-only change. Existing implementation
and semantic reviews below retain their bounded scope.

The successor `CandidateInference` no longer recognizes the exact
`ShadowLocalBind` fixture in preflight. Graph collection no longer looks up or
emits that fixture. Generic `LocalSource` formation owns lexical local programs;
ordinary retained expressions continue through their compositional recipes.
Fixture-only artifacts cannot be reinterpreted as authentic generic source.

The ledger removes active `CTX_FINITE` and its three edges, including the
`JOINT_DEC` prerequisite. Its finite context/static-port enumeration and sealed
packet presentation are not inputs to the actual Simple-sub worklist. A separate
retirement record preserves the reason; no theorem is marked proved. Historical
SD-NPB is removed from directly reused closed lemmas for the current solver.
`JOINT_DEC` remains OPEN-PROOF with complete solving/residual meaning,
preservation/reflection, completeness, termination and resource requirements.
GENERALIZE and HIR_WIRING now describe the actual live-level generic source route.

## Verification and review

The independent dependency/conformance review found no issue: only the retired
node disappeared, and every surviving status, premise and production-authority
field was preserved. The implementation/regression review found one major in
the new test input: anonymous lambda expressions are outside current generic
source formation. A fresh producer replaced it with the supported named
`apply` declaration, keeping the late constraint and graph/effect assertions.
Fresh semantic delta review closed that repair without further findings;
production edits were unchanged. All assigned reviews are adjudicated and closed.

Focused checks (all Cargo commands used `RUSTC_WRAPPER=`, `timeout 180`,
`--offline`, `-j 2`; tests also used `-- --test-threads=1`):

- `cargo test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement`:
  final 5 passed. Initial run was 4 passed / 1 invalid source fixture; corrected
  declaration-form input passed without weakening expected graph assertions.
- `cargo test -p yu-solver --features shadow-apply-candidate --test shadow_apply_candidate`:
  19 passed, preserving historical observer clients and ordinary behavior.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_graph_call_`:
  2 passed, 476 filtered; actual expression graph Call route retained.
- `python3 tools/research_successor_obligation_dag.py`: passed; 89 nodes,
  193 edges, 32 families; generated artifacts current.
- Scoped diff/whitespace checks passed.

The generator is a ledger consistency checker, not a semantic proof checker.
No benchmark or performance experiment is required for this dispatch removal;
measurement budget is zero. Removed fixture lookup does not add traversal or
allocation; generic source construction is the existing path.

`cargo check -p yu-solver --all-targets --features shadow-apply-candidate`
passed without warnings using the same bounded Cargo options. Workspace-wide
tests, runtime backend suites, complete semantic proofs and public cutover were
not run or certified by these focused checks.

## Remaining migration

Historical `CandidateValueObservation` still has actual public crosswalk clients
and uses `preflight_local_binding` / `emit_candidate_local_value`. Those clients
and their F5 closed schemes require a separate coherent migration before deleting
the shared historical helpers. Default `ConstraintBatch::collect` still uses F5;
the private successor has not replaced production inference.

The [candidate closed lifecycle retirement](2026-10-10-candidate-closed-lifecycle-retirement.md)
subsequently removed candidate finalizer/closed-scheme ownership. The
[unused draft resource withdrawal](2026-10-10-candidate-unused-draft-withdrawal.md)
now removes its remaining startup draft reservation. These actual candidate
dependencies are withdrawn; the legacy public clients described above still
need their genuine closed owners.

The historical pure observer's fixed-empty Apply/Group effect route remains in
that observer, not in the successor graph route. Complete Call construction and
source/effect annotation formation remain real outstanding work. Registry-before-
basic-constraint-generation is not restored as a prerequisite by retaining those
semantic obligations. Current graph fields and pending markers do not prove
complete provider/world/effect correspondence.

Complete Call, effect hygiene, soundness and principality retain their genuine
requirements. This bounded withdrawal is a checkpoint in the active inference
goal, not full legacy retirement, theorem closure or F5 cutover.
