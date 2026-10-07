# Shadow R-origin characterization — round 10

Baseline: fetched `origin/research/simple-sub-intrusion` at
`6187ed18e83e93fa0548cbb92a85bb0a1f54bfd4`; the local branch matched before
the change. The canonical successor DAG started and ended at 90 nodes / 196
edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19,
IMPLEMENTATION-ONLY 1. No semantic status changed.

## Focused current-identity fixture

The opt-in receiving-origin capture previously had a nonempty-Q fixture but
no dedicated nonempty-R fixture. The new source
`my f x = f; pub alias = f` gives the receiving alias scheme a nonempty
recursive binder inventory. Its test joins the exact source occurrence to the
incoming use, target scheme, receiving scheme and captured historical rows.
For every receiving R binder, it requires exactly one origin and exactly one
matching recursive fresh row from that incoming use. It also checks stable
repeated observation, separation across two solves of the same collection,
unchanged observation counters, and the three pending successor premises.

An independent compiler-referee review passed with no findings. The review
confirmed the assertion is only historical current-solver row identity; it
does not claim successor semantics, eligibility, source adequacy, or Q/R
correspondence. The unresolved generalization, successor Q/R correspondence,
and shared-contract transport premises remain explicit.

Checks passed:

```text
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test -p yu-solver \
  --features shadow-f5,shadow-scc-observer \
  --test shadow_receiving_root_scheme_crosswalk \
  recursive_alias_receiving_origin_retains_exact_incoming_fresh_row \
  -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs
git diff --check
python3 tools/research_successor_obligation_dag.py
```

The focused test passed (1 test; 2 filtered). The DAG validator passed. No
broad suite, build, performance measurement, semantic implementation, or
production path change occurred.

## Next attack

Continue the dependency-ordered semantic attack on CALL_TYPE's smallest joint
argument/actual-provider whole-carrier constructor, ORIGINAL_ASSOC P2's
source-owned complete-contribution introduction, and REC_DESC's competing
finite-history versus direct two-closure route. This test is not evidence for
any of those source rules and does not close a DAG obligation.
