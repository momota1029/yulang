# Contextual closed-Allowance replay checkpoint (2026-10-10)

The private Simple-sub candidate now carries exact relation identity through
typed work scheduling. Distinct contextual relations sharing the same endpoint
pair remain separately reachable, and their discharge state, processing
relation, adjacency and rollback accounting stay in the contextual relation
store. A covariant closed source annotation creates an executable Allowance
check before endpoint memoization or self omission; the normal bound continues
to check later lowers on the true receiver.

Independent review found that an already registered Allowance could discharge
a newly admitted contextual relation without attaching that relation to the
existing bound. The repair now records the new bound origin before discharge,
so the retained replay dependencies make an existing conflict observable at
the new source occurrence. A focused regression covers pre-registration,
existing conflict, rollback and retry. The independent compiler-referee delta
review found no remaining issue in this closure scope. The spec audit also
identified a stale work-item size assertion: the default build keeps its prior
assertion, while the candidate build checks storage for both the task and its
relation handle.

Focused checks passed:

- `cargo test -p yu-solver --features shadow-apply-candidate candidate_context::tests -- --test-threads=1` (15 passed).
- `cargo test -p yu-solver --lib f5b_structured_duplicate_replays_one_canonical_witness_for_its_new_source --offline -- --test-threads=1` (1 passed).
- The same focused layout test with `--features shadow-apply-candidate` (1 passed).
- `git diff --check`.

No broad suite, benchmark, or timing measurement ran. `rustfmt --check` on the
two contextual files reported formatting differences across the existing
context implementation, so no whole-file formatting rewrite was applied.
This closes only executable closed-Allowance filtering and replay in the
candidate path. General contextual operation propagation, residual recipes,
certified-cycle invalidation, complete effect hygiene, Call, public/default
inference, soundness/principality and F5 retirement remain open.

Next: continue the approved contextual relation gate by transporting exact
operation contexts through bounds, extrusion, capture/freshening and qualifying
intrusion, then implement the selected cycle lifecycle without widening source
admission.
