# Value-occurrence intrusion implementation

Status: reviewed private implementation checkpoint; no public/F5 cutover
Branch: `research/simple-sub-intrusion`
Baseline: `af1ebfd211865e9632bd8bd8449c9b72f3144433`
Authority: the user's direct implementation request, the
[top-level principles §1.1](../design/2026-10-11-yulang-inference-top-level-principles.md#11-source-constraints-and-intrusion-direct-clarification-2026-10-14),
[occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
and [source Value references](../design/2026-10-10-parent-copy-scc-intrusion.md).
Mode: M3; pre-write spec review, semantic review and static performance review.
Measurement budget: zero benchmark processes and samples.

## Implemented correspondence

`candidate_value_graph` constructs resolved module, local, parameter and
expression Value identities independently of solver rows. Definition roots own
their source Name references; nested initializers belong to their own local
roots. Apply fragments retain the approved Name/nested-Apply membership.
Group/ascription callee resolution preserves the actual resolved binder.

Fragment helpers share nested source fragments. A path with only helper
vertices in its interior projects to the original resolved Name-reference edge;
every approved edge expands into such a path. Original Value reachability and
SCC membership are therefore preserved. Containment creates no semantic edge
from an outer Apply result to an inner result. Construction and SCC traversal
are linear in the source/graph incidences, plus source identity payload work.

Call checking occurrences seed immutable origin/receiver associations. Relation
identity retains whole association handles through queued work, Function ports,
bound replay, canonicalization and fresh-use transport. A replay combines whole
association handles, never a cross product of separately gathered endpoints.

Each actual extrusion records its polar Value/Effect parent-copy pairs and
occurrence identity. Original records remain immutable. Reuse of a retained
transformed memo child creates a separate occurrence referencing the exact
original pair group. Qualification uses the source Value SCCs, and actual row
equality retains bounds, levels and contextual consumers. A source-less type
cycle does not qualify.

The final settlement repair uses the frozen graph and immutable association
sets: a qualified original pair or first qualifying reuse contributes its
equality once. Pending indices, their consumed cursor and group activation
history are restored by the existing transaction owner on rollback. This
avoids expanding historical reuse records into duplicate equality candidates.

## Review and fixture repairs

Pre-write `spec_auditor` approved replacing obsolete type-bound cycle fixtures
with real source SCCs and actual occurrence associations, while preserving
their equality, propagation, context and diagnostic assertions. The acyclic
control now refers to distinct source components. Multi-definition fixtures use
newlines and assert parse/source health before checking inference.

The first independent semantic review found mutable occurrence ownership on
memo reuse. The first repair introduced immutable pair groups and separate reuse
records; semantic delta review closed that finding and the fragment projection.
Static performance review found repeated Apply subtree expansion, repeated
whole-table byte accounting and recapture provenance amplification. The first
repair closed those costs. Its delta identified duplicate settlement expansion
and missing construction scratch; the final repair addresses those owners.
Independent semantic and performance delta reviews closed both findings with
no remaining blocking or major findings in the inspected implementation scope.

## Verification

All Cargo commands use `CARGO_BUILD_JOBS=2`, a 300-second timeout and one test
thread. The final frozen implementation passed:

- `cargo check -p yu-solver --features shadow-apply-candidate` passed without warnings.
- `cargo check -p yu-solver` passed without warnings.
- `cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests -- --test-threads=1`: 15 passed.
- The corresponding `candidate_context::tests` filter: 117 passed.
- Integration targets `candidate_local_self_recursion`, `candidate_lifecycle_retirement`,
  `shadow_candidate_source_crosswalk`, `shadow_candidate_multiroot_source_crosswalk`
  and `candidate_value_entry_effect`: 14 passed, with
  `-- --test-threads=1 --skip two_recursive_calls_constrain_one_monomorphic_initializer`.
  The known baseline test below is the only exclusion.
- `git diff --check` passed.

The unmodified `candidate_local_self_recursion` suite initially gave four passes
and one failure in `two_recursive_calls_constrain_one_monomorphic_initializer`.
An isolated run at exact baseline `af1ebfd21` reproduced the same assertion
(`recursive.len()` was 3, expected 2). `fresh_use` intentionally returns no
observation whenever the candidate has any conflict; the test simultaneously
requires a conflict and interprets absent observations as recursive routing.
Neither that test nor its observation API is changed here.

The additional deterministic tests use T=12 original pairs and K=8 qualifying
reuse records, both initially qualified/unqualified and with both kinds and
polarities. Only T equality candidates are registered. Another test activates
an existing group, rolls back its cursor and activation, then retries. Source
graph checks at 8, 16, 32 and 64 nested Applies establish the bounded storage
discriminator without timing measurements. The total final runtime coverage is
146 passing tests; it is not a proof of the general algorithm.

No broad workspace suite or timing benchmark has run; the selected gate is the changed solver responsibility and
its source, context, lifetime and effect-entry consumers.

## Remaining scope

This checkpoint covers private LocalSource call-demand associations. It does
not establish source-global extrusion correspondence, equality preservation,
soundness, principality, complete Call or public/F5 cutover. The private carrier
still lacks If/Boolean/String construction, so the user's branch-union example
is not an executable test of this carrier yet. Existing hygiene results remain
available; their missing executable constructor/consumer bridge is a separate
implementation responsibility.

Source-set interning and replay retain costs in the number of distinct source
subsets and relation combinations. No overall linear inference claim is made.
Pending questions are excluded from this checkpoint's integration scope.
The primary synchronized `tasks/current.md`, the governing association record
and design index alongside this implementation record. Earlier historical
research records retain their original theorem status.
