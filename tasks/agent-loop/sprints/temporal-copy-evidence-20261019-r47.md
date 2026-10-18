# Sprint R47 — authenticate temporal copy evidence for scoped Apply

Status: ACTIVE, revision 1
Branch / baseline: `research/simple-sub-intrusion` / `3860c5d2bac12efde6fb543ba68a637ef47a9ab2`
Parent: unchanged full inference/evaluator theorem and original Simple-sub A/B, original quantifiers, source domain and accepted semantics; **OPEN, 0 → 0**.

## Fixed outcome

Repair and validate the existing test-only scoped-Apply capture/reconstruction
candidate so that it retains evidence from the actual capture, reconstruction,
intrusion-merge and inspection points. Demonstrate an owner-authenticated
later canonical-row hit that reuses a previously allocated fresh image and has
`image == existing_image != source_representative`. Preserve an explicit
temporal edge between the reconstruction-time source representative and the
later inspected state, or report `MISSING_RETAINED_EVIDENCE` at the exact
owner if the implementation does not retain enough information.

Apply the result to the original inference/evaluator parent as a bounded native
transport prerequisite only. No source `Desc`, `D_q`, Application/Call rule,
accepted source behavior, theorem gate or production authority is created by
this sprint.

## Parent scope and boundaries

The full inference/evaluator theorem and original Simple-sub A/B retain their
original quantifiers, source domain and semantics; they remain **OPEN 0 → 0**.
This sprint may repair only test-only observation and validation for the
existing candidate capture/reconstruction route. Every added temporal
observation field and event log must be under `#[cfg(test)]`; production
behavior, allocation, solver order, source admission and failure behavior must
remain byte-identical outside test configuration. If the proof requires a
production invariant or a new source rule, stop and return that precise owner
and premise to Luna.

Do not infer historical identity from current `rep(...)`, a generation counter
alone, equal endpoint shapes, selected first rows, or a successful query. Do
not weaken the accepted source domain, alter expected outputs, or turn an
instrumented test into a theorem. Preserve the existing negative substitutions
and add no workaround that changes source admission to make the target event
occur.

## Exact baseline and direct dependencies

Baseline commit: `3860c5d2bac12efde6fb543ba68a637ef47a9ab2`. Existing tracked
or working-tree observations below are immutable inputs; the R47 implementation
lease may continue only the exact `candidate_scheme.rs` test-only overlay named
below. Recompute hashes before accepting any result.

| Dependency | SHA-256 | Use |
|---|---|---|
| `notes/progress/2026-10-18-r37-rev3-review-closeout.md` | `5c1aa3ea9f653a73d5f7466f61f9cbc32bc641fcc56ac5eeed6ff3da201f1d44` | Exact vacuity and missing temporal-edge findings |
| `tasks/agent-loop/sprints/authentic-apply-copy-bridge-20261018-r37-rev3.md` | `b19c4131f79476f787b8ef424e46f38a396598234dab5400215025938bd0d250` | Frozen candidate claim and original limits |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` | Existing test-only capture/reconstruction candidate; primary-owned overlay |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` | Merge and undo owners; clean baseline |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Source scheduling and event sequencing |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Solver drain and rollback lifecycle |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Candidate Apply source/native ports; read-only overlay |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Exact fixture and existing test intent; read-only overlay |
| `notes/progress/2026-10-19-r46-closeout.md` | `b39e5957cf85d23020163319613a77deb1a5db1a63ece71eeaa481d11d5f0a72` | Latest parent/source boundary and preserved Apply occurrence result |

## Method and exact leases

### Luna — bounded test-only implementation and source-owner map

Inspect `GraphBuilder::row`, `prepare_candidate_fresh_use`,
`merge_candidate_rows`, source scheduling, solver drain and the corresponding
undo path. Add only the minimal `#[cfg(test)]` observations at their actual
owners needed to distinguish capture time, reconstruction time, each later
merge/rollback transition and inspection time. Repair the current test
predicate so a later map-hit row is selected by its own owner record rather
than the first row in a final equivalence class. Keep the earlier fresh-image
allocation and later image reuse distinct.

Exact write leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_intrusion.rs` (test-only observation fields/hooks only)
- `notes/progress/2026-10-19-r47-temporal-copy.md`
- `tasks/agent-loop/inbox/20261019-r47-implementation.md`

All other dirty paths are read-only. No expected-output, public API, language
semantics, non-test production behavior, or unrelated test edits.

### Sol — independent temporal correspondence proof and falsifier

Independently derive the temporal relation from the pinned owners. Distinguish
the key requested by capture, representative retained at capture, source
representative selected during reconstruction, reused canonical image, later
intrusion merges, and any journal rollback. State which owner record proves
each edge and whether rollback invalidates or restores it. Apply this exact
invariant to the R37 observation claim and original native transport premise.

Reject current-state `rep(...)` as historical evidence, generation-only
arguments, forged observations, first-row selection, vacuous map-hit branches,
or a test whose fixture never traverses the claimed event. If an owner does not
retain the needed transition, return `MISSING_RETAINED_EVIDENCE` with the exact
source owner; do not assume stability or change production semantics.

Exact write leases:

- `notes/theory/2026-10-19-r47-temporal-copy-refinement.md`
- `tasks/agent-loop/inbox/20261019-r47-proof.md`

### Fresh independent review and gated execution

After both lanes freeze, Luna assigns fresh independent compiler and spec
reviews over the same frozen source/contract/proof/test snapshot. Reviewers
must check the capture→reconstruction→merge→rollback temporal chain, an actual
nonvacuous later hit with `image == existing_image != source_representative`,
the exact q/helper routes, all negative controls, and that production behavior
is unchanged. Only after both reviews are clean may Luna run one focused test
invocation against the reviewed bytes. Any repaired bytes invalidate reviews
of those bytes and require a narrowly scoped fresh review before test execution.

Exact review leases:

- `notes/progress/2026-10-19-r47-compiler-review.md`
- `notes/progress/2026-10-19-r47-spec-review.md`

Verification command, one owner/process, only after clean reviews:

```sh
RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_scheme::authentic_demand_capture_tests::active_outer_root_two_helper_uses -- --exact --nocapture
```

If the module path does not match the actual test binary, Luna must resolve it
from the frozen test declaration before execution and record the exact command.
No other build/test/runtime process is authorized.

## Resource envelope and stop conditions

Total cap **3000 seconds**, no carryover: Luna test-only mapping/implementation
900; Sol proof lane 900; fresh compiler/spec reviews 300 each; one gated focused
Cargo test 180; Luna integration 420. Astra 0. Reserve and conservatively
charge every grant when issued. CPU/RSS are UNKNOWN unless measured. Use one
heavy Cargo process only after review; no parallel build or nested CLI.

Stop at a reviewed and exercised temporal correspondence, exact
`MISSING_RETAINED_EVIDENCE`, an earlier concrete execution obstruction,
dependency/authority change, lease conflict, or budget bound. Parent remains
OPEN absent a complete independently reviewed proof/refutation. No ordinary
Application formation work is included; R41's unadopted rule candidate and its
approval gate remain separate.

## Primary grant

This packet changes the method from final-representative comparison to
owner-recorded time-indexed refinement of the same existing capture and
reconstruction events. Luna grants only the exact test-only observation and
review leases above. Primary retains current-state, review appointment,
adjudication, shared-record synchronization, staging, commit and push duties.
