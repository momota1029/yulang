# Shadow parameter-to-row bridge — round 12

Baseline: fetched and pushed `origin/research/simple-sub-intrusion` at
`ee2f22c04af762a4229f5b3d2dc943df8584c968`. The canonical successor DAG
remains 90 nodes / 196 edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43,
OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1. No semantic status changed.

## Captured identity

The default-off solver shadow now retains `(HirParameterId, historical row)`
for the exact parameter recipes allocated at session startup. This uses the
same checked startup mapping as current Lambda admission:
`parameter_live_base + recipe_position`. Capture is initialized after the
startup allocator has completed, so unsupported bodies still retain their
allocated parameter row even where no `LambdaRecipe` was admitted. It adds no
row and reads no inferred type shape.

`SolvedModule::shadow_parameter_row` uses the existing solve-branded
`FreshRowRef`. It distinguishes NotRequested, Unavailable, NoProductionRecipe,
and Captured. It checks exact HIR ownership before returning a row. An outer
production parameter in the nested local-Apply fixture has a captured row;
the local `step` parameter has no production recipe and is reported absent.
Its Application remains `ApplicationTypingRuleUnresolved` with zero facts.

The identity evidence does not establish source denotation, eligibility,
successor binder order, typed Apply, or any source/successor semantic
correspondence. Capture remains opt-in, private until successful solve
publication, and disconnected from ordinary inference. If optional evidence
reservation fails, the shadow view is Unavailable and production solve
continues unchanged.

Independent compiler-referee review passed with no findings. The review
checked the startup identity arithmetic and overflow justification, exact
parameter ownership, local/foreign behavior, optional allocation failure,
publication, parity, and unresolved premise boundaries.

Checks passed:

```text
RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 \
  --test shadow_parameter_row_identity -- --test-threads=1
RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 --lib \
  shadow_parameter_capture_unavailable_preserves_production_result \
  -- --test-threads=1
RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-f5,shadow-scc-observer
RUSTC_WRAPPER= cargo check -p yu-solver
rustfmt --edition 2024 --check crates/yu-solver/src/shadow_f5.rs \
  crates/yu-solver/tests/shadow_parameter_row_identity.rs
git diff --check -- crates/yu-solver/src/lib.rs \
  crates/yu-solver/src/shadow_f5.rs \
  crates/yu-solver/tests/shadow_parameter_row_identity.rs
python3 tools/research_successor_obligation_dag.py
```

The focused integration target passed 2 tests; the simulated unavailable-state
unit test passed 1. Package checks passed with shadow features and without
them. The whole-file rustfmt check on `lib.rs` reports existing repository
formatting drift; no unrelated reformatting was applied. Actual allocator
exhaustion was not induced; the test injects the resulting unavailable state.
No broad suite or performance experiment ran. Retention is one pair per
parameter recipe and occurs only in the requested shadow lane.

## Next attack

Continue from the exact source-owned producer boundary: connect parameter and
occurrence identities to complete source-coordinate and fixed-dependency
coverage only when independently derived. Keep `CALL_TYPE`'s actual-provider
checking, `ORIGINAL_ASSOC`'s source introduction, `REC_DESC`'s cyclic
acceptance, generalization eligibility and source adequacy open. Production
inference replacement and cutover remain gated.
