# R280 — constructor-derived validity at R70 extrusion entry

Status: admitted for Sol owner-coverage gate only. The proof stage is NOT
GRANTED unless that gate passes and Luna freezes an indexed production view.
The active parent remains the unchanged Yulang inference/evaluator goal,
including its accepted source domain, quantifiers, Simple-sub A/B and semantics.
Branch `research/simple-sub-intrusion`; no baseline movement is planned.

## Fixed outcome

Derive from actual initialized sessions and permitted successful/failure/resume
histories only the row/storage component of the existing R70 entry predicate W
at both production `dispatch_live_item -> candidate_extrude` branches. Apply
exactly that component to unchanged parent edge
`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` in `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md`.

The target component is: Value/Effect bound, level, metadata and representative
storage stay aligned; every reachable row ordinal belongs to its matching
kind table; representative forests are finite, in-range, kind-separated and
preserve the recorded lane; bound endpoints admitted or restored by an actual
constructor have the endpoint kind and lane polarity required by their owner;
level mutation/merge preserves valid level entries and the production entry's
target row is valid. Derive initialization, fresh-row allocation, bound
insertion/readback, representative merge, extrusion copies, FreshUse and
restoration, plus failure/resumption ownership. State only the clauses actually
proved and apply them explicitly at each callsite. Do not assume W or construct
an arbitrary malformed native state as a source counterexample.

Leave term/view/incidence validity, source/evidence completeness, replay drain,
R71 canonical-fiber coverage, `Need_D`, other R70 W clauses, F1/FK1 and whole
soundness open wherever not proved. Parent/A/B remains 0->0 absent justified
application. A reachable wrong-kind/out-of-range ordinal, mismatched parallel
table, cross-kind representative, invalid restored bound, or failure state
that can resume into dispatch falsifies the corresponding clause.

## Authority and exact inputs

Governing authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
(SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`),
`rules/goal-driven-sprints.md`, and the unchanged R70 source/theory contracts
below. R255 is used only as an authenticated workspace path/hash inventory;
none of its proof claims are premises.

- R70 theory: `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md`,
  SHA-256 `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7`.
- R70 contract: `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md`,
  SHA-256 `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`.
- Authenticated workspace inventory: R255 contract
  `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256
  `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
  Verify its 36 listed path/hash rows exactly before any source body read.
- Additional exact in-workspace owner admitted by Luna: `crates/yu-solver/src/candidate_context.rs`,
  SHA-256 `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.

The intended owner set is the pinned solver `lib.rs`, `term.rs`,
`candidate_extrusion.rs`, `candidate_intrusion.rs`, `candidate_scheme.rs`,
`candidate_source.rs`, `candidate_context.rs`, `candidate_effect.rs`,
`candidate_scope.rs`, `candidate_value_graph.rs`, and `shadow_apply.rs`, only
where exact production intervals supply or mutate this component. Search may
identify further owners only within the 36 authenticated R255 workspace paths.
If a required helper is outside those paths, report its exact path/symbol and
STOP before opening it; Luna must version the contract and grant that path.

All source reads are limited to exact indexed production intervals after Luna's
initial hash and scope gate. Exclude `#[cfg(test)]`, test bodies, external
registry/library bodies, parser/classifier, runtime/quarantined paths and any
non-inventoried source. No test, build, Cargo, Lean, probe, code edit, semantic
change, expected-output change, Git operation or nested CLI is authorized.

## Stage gates and resources

One Sol/high `prover`, no descendants. Proposed identity
`/root/sol_r280_extrusion_entry_validity`; coordination session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested model/effort: gpt-6.1-sol/high;
record observed values only from runtime evidence.

1. **Owner-coverage gate: 300 seconds, GRANTED.** Read this contract and
   authenticated parent/authority records; verify all 36 R255 rows and the
   additional candidate_context pin; locate every production constructor,
   writer, level change, merge, restoration and return/resume route needed for
   the target component. Return a complete path/symbol/interval coverage map,
   or exact missing owner and falsifier. This stage grants no proof/output
   writes and must STOP INCOMPLETE if any writer/restoration owner is missing,
   initialization is assumed, `live_variable` is treated as row-existence
   proof, or an error/resume route is unexplained. No body outside the listed
   pins may be opened.
2. **Constructive invariant/application: 2,400 seconds, NOT GRANTED.** Luna
   grants separately only after stage 1 passes and Luna freezes an indexed,
   production-only view and exact output leases. Produce the strongest justified
   row/storage preservation result and apply it to both unchanged R70 entries.
3. **Fresh independent compiler review: 1,200 seconds, NOT GRANTED.** After
   producer freeze, with exact reviewer identity and frozen hashes.
4. **Luna preparation/adjudication: 600 seconds.**

Total ceiling 4,500 seconds; no reset, renewal, Astra, or descendants. Charge
issued reservations in full unless stronger current runtime receipts establish
actual accounting under policy. Preserve all R279 charges and its INCOMPLETE
STOP; do not reopen the external-body witness.

## Status boundary

No production edit is authorized. Implementation remains `NO_SAFE_CODE_SLICE`
unless a reviewed reachable violation of an approved clause is established and
Luna separately grants an exact code lease. A conditional component does not
close W or R70. R70/R71/Need_D and original Parent/A/B status remain open until
a justified result is applied at its unchanged parent edge.

Future exact output leases, granted only after the owner gate passes:

- `notes/theory/2026-11-03-extrusion-entry-validity-r280.md`
- `tasks/agent-loop/inbox/extrusion-entry-validity-r280.md`

Review receipt path:
`tasks/agent-loop/history/20261103-r280-extrusion-entry-review.md`.
