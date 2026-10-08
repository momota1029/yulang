# Identity SourceBuild failure-policy production map

Date: 2026-10-08
Status: non-authoritative research audit; no failure policy selected
Packet baseline: `research/simple-sub-intrusion`, HEAD `8f2c5a8e2` (provided by primary; no Git command run)
Frozen input: [id SourceBuild owner draft](../design/2026-10-08-id-sourcebuild-owner-design.md)
Input SHA-256: `785a5a4d5133d8c1790e1e0a5f85f19bab83e0d0c84c502951ab6f80f1596bca`
Method: adversarial reading of production control/data flow and direct-call-site inventory; no builds, tests, measurements or production edits
Output lease: this file only; shared records and Git belong to primary

## Scope and governing boundary

This audit applies to the draft's pre-session producer, complete-or-absent
staging, terminal retention, and the failure alternatives in §§5–6. The draft
is not implementation authority. `rules/design-authority.md` requires explicit
approval for a changed API/resource/failure boundary; `rules/compiler-engineering.md`
requires the error cause to retain its actual owner and structured meaning.
`rules/testing.md` permits a record-only narrow inspection; no executable
verification was requested by this packet.

The bounded Rust search found no `compile` entrypoint, `CompileError`,
`compile_counted`, `compile_with_counters`, or `SolveError` in this workspace.
The actual error names are `SolveAvailabilityError` and `SolverError`.
`crates/yu-core/src/lib.rs:1` is currently a module boundary, not a compile
wrapper. Searches for `SolvedModule::solve` outside yu-solver found no direct
production caller. Located callers are yu-solver unit/integration tests; their
implementations and expectations were not audited. A separate compile wrapper,
user-facing diagnostic renderer, or caller recovery policy is therefore a
missing premise, not inferred behavior of this branch.

## Exact production path

All line references in this section refer to `crates/yu-solver/src/lib.rs`.

| Boundary | Existing owner/control flow | Consequence for a candidate sidecar |
| --- | --- | --- |
| Collection (`:855`, `:1330`) | `ConstraintBatch::collect(Arc<HirModule>)` consumes an Arc handle and returns a collected batch or collection error. `collect_mode` builds and seals one SCC plan, accounts it, then returns `Ok(batch)` at `:1337`. | A post-collection/pre-session constructor can inspect HIR and the sealed plan. It has no source semantic owner payload today. This is before the live solver, not before baseline collection allocation. |
| Solver entry (`:16027`) | `solve(batch: ConstraintBatch) -> Result<SolvedModule, SolveAvailabilityError>` calls `InferenceSession::try_new(batch)?.run()`. | The argument moves. An `Err` returns neither batch nor live session. No caller-owned session exists to resume. A candidate early metadata rejection still consumes the solve argument unless a distinct internal preflight is placed before that move. |
| Startup (`:9402`, `:9441`, `:9610`) | `try_new` computes capacities; `Self` owns `batch` and a new branch store. `reserve_startup!` reserves solver lanes fallibly before publishing live row identities; the final resource sample precedes `Ok(session)` at `:9772`. | Package construction before `try_new` avoids solver mutation during construction. Retaining a successful package across startup nevertheless changes live allocation coexistence. |
| Solver attempt (`:9969`) | `run(mut self)` admits collected facts, executes the SCC plan, samples/finishes store accounting, then calls `self.finish()`. Each `?` terminates this owned attempt. | Isolation of the metadata producer must include admission/store/provenance/row/finalization state. Existing internal route rollback does not turn the public solve API into a resumable API. |
| SCC execution (`:13125`, `:13136`) | Private execution borrows the batch's recipes/plan and installs finalized member schemes during the attempt. | Scheme installation is a solver event; it is not the source binding-publication supplier. A metadata error after schemes are installed can suppress the entire returned result. |
| Finish pre-transfer (`:15740`, `:15813`) | `finish(mut self)` constructs projection output; samples coexistence; takes the finalization owner; finishes it fallibly; updates the closed arena accounting; releases substitution scratch. | A metadata validation/reservation inserted here adds a possible late failure after inference and/or closed finalization. This cannot be called rollback to a live F5 session. |
| Counter/result transfer (`:15899`, `:15949`, `:15970`) | Finish combines batch/store/projection/execution counters, takes errors, then constructs `Ok(SolvedModule { ... })`. HIR, projections, root index, schemes, closed arena, route provenance, errors, store and counters move to the result. | The candidate can move only a complete staged package at this final construction. The batch SCC plan, collected definitions and Parameter/Lambda recipes are not transferred as corresponding result fields; any retained owner dependency on them must have an independent lifetime. |
| Public observations (`:16060`, `:16066`, `:16072`, `:16085`, `:16100`) | `hir`, `errors`, `store`, `counters`, `projection_for`, and `root_value_for` expose retained F5 data. Root queries increment result atomics. | Private absence currently has no public projection or diagnostic. A producer that invokes counted queries can change public counters despite borrowing read-only data. |

`SolvedModule` fields are at `:7333`; `InferenceSession` fields at `:7419`.
Neither currently has a SourceBuild package, metadata absence reason, or
metadata-failure field. Terminal Rust ownership transfer supplies no semantic
source publication or anchor evidence.

## Current failure and diagnostic vocabulary

`SolveAvailabilityError` (`:3845`) is a copyable enum with only
`ArtifactMismatch`, `CauseMismatch`, `ReceiptMismatch`, and `IdentityExhausted`.
`From<ConstraintError>` (`:3851`) maps existing store/identity failures;
`CrossKind` is explicitly a local error rather than an availability error.
There is no metadata-missing, source-law-supplier, allocation-cause, or
SourceBuild-invariant variant or payload.

`SolverError` (`:3828`) contains an actual constraint occurrence, cause, and
`SolverErrorKind`; the only kinds (`:3810`) are `CrossKind` and
`IncompatibleValue`. Cross-kind admission appends a local error at `:10768`;
`report_incompatible` (`:12618`, append at `:12657`) deduplicates and retains an
actual relation error. These errors are transferred inside `Ok(SolvedModule)`
and exposed by `errors()` (`:16066`). Thus `Ok` means a total available solve
artifact, not proof that every relation or source has no errors. A missing
semantic supplier is not either existing relation error, and appending a fake
one would change diagnostics and its provenance meaning.

Existing invariant panics are visible: `map_finalization_error` (`:9775`)
maps `IdentityExhausted` but panics for internally invalid drafts; finish
asserts closed-finalization receipt continuity at `:15831`. These are existing
F5 responsibility boundaries. Their presence does not select a panic/abort
policy for a new private metadata producer. A panic is not identical to
process abort: unwind versus termination depends on panic configuration and
caller handling, neither supplied by this packet.

## Decision table: candidate outcomes, not selected behavior

For each row, “unchanged F5” is conditional on the existing solver attempt
remaining available under the added resource coexistence. The following
section explains why a stronger resource-state acceptance claim does not
follow.

| Candidate and triggering condition | Result/acceptance consequence | Diagnostic and counter consequence | Ownership/discard consequence | Can existing public APIs express it faithfully? |
| --- | --- | --- | --- | --- |
| Optional sidecar: structural `NotApplicable` | Continue ordinary solve; no certified package. | No new diagnostic. Existing counters can remain identical only if preflight uses uncounted inputs. | No partial package retained; preflight precedes metadata allocation. | Existing `Result` need not change; new private absence/storage representation is required. |
| Optional sidecar: missing authentic supplier | Continue ordinary solve with explicit private absence; absence proves nothing about source validity. | No relation error or availability error attributable to the missing premise. Existing counters require isolation. | Drop isolated staging and all exclusively staged owner references. | Public success can express continuing F5, but current structures cannot record the distinct private reason. A private outcome is needed; no new public API is required solely for absence. |
| Optional sidecar: catchable metadata allocation failure | Discard metadata, then attempt ordinary solve. | No new diagnostic/counter charge under the draft's isolation contract. | Drop the whole incomplete staging region; do not transfer a prefix. Teardown itself must be safe/bounded. | Compatible with current public return shape if intercepted inside the metadata owner. Allocation manifest/fallible constructor coverage are absent. |
| Optional sidecar: internal defect, discard-only arm | Continue ordinary solve with no package. | No new diagnostic; no counted mutation survives. | Entire staging discarded. This keeps an uncertified package out of the result; it does not certify the failed constructor. | Public return shape supports continuing, but a new private outcome/validation boundary is needed. Policy selection and isolation proof remain open. |
| Optional sidecar: internal defect, surfaced `Err` arm | An otherwise available F5 result may be withheld. | Caller sees an availability failure; no retained `errors()` or final result counters are returned. | Owned batch/staging, or live session if late, are consumed/dropped. No resumable solve is returned. | `Result::Err` exists, but current variants faithfully encode only their existing concrete mismatch/exhaustion causes. Duplicate owner, omitted clause, and missing postcondition have no faithful variant. New structured error vocabulary would be an API decision. |
| Required metadata: missing supplier for admitted shape | Prevent a successful available result, even if F5 could solve it. | New availability boundary; not malformed-source or relation diagnostic. Final result counters are absent. | Reject at the approved phase; drop staging and whatever baseline owner is consumed there. | No existing error variant records this cause. Mapping it to `IdentityExhausted` misstates/collapses the cause. Requires approved behavior and a faithful error channel. |
| Required metadata: catchable allocation failure | Prevent a successful available result. | Existing enum can syntactically return `IdentityExhausted`, but loses metadata cause versus existing solver exhaustion. Whether that coarsening is acceptable is unresolved; the draft requires cases to remain distinct. | Pre-session rejection avoids creating a live solver. Late rejection destroys an owned attempt/result candidate instead. | Coarse inability is expressible; the draft's distinct-cause contract is not presently expressible through the enum. |
| Required metadata: invariant defect returned as structured failure | Prevent available result. | Must expose the actual internal cause rather than forge a `SolverError`; no final result counters. | Drop complete staging/attempt at the selected boundary. | A genuine artifact-brand mismatch may match `ArtifactMismatch`; all defects cannot be relabeled this way. Other new causes require approved vocabulary. |
| Abort-on-invariant candidate (optional or required): internal defect | No normal result is returned; process termination if an explicit abort is chosen. A panic alternative has separately unresolved unwind semantics. | No structured solver diagnostic/result counters. Panic text or process exit is a new observable failure surface. | Explicit abort does not run normal destructor cleanup; unwind may drop owned staging/session, but no API rollback follows. | Termination bypasses the `Result` API; the existence of F5 panics supplies no approval for this new behavior. |
| Any candidate: infallible/process-aborting allocation failure | No recovery promise from the optional/required policy follows. | No guaranteed structured diagnostic or final counters. | Normal discard may never run. | Existing APIs cannot turn a process abort into metadata absence. Fallible reservations do not cover later infallible allocations. |
| Defer integration | Existing solve path only. | No new metadata outcome or observations. | No metadata owners created/retained. | Directly matches current production structures. |

## Adversarial falsifiers resolved by implementation reading

1. **A borrowed query is not necessarily uncounted.**
   `definition` (`:1434`), `definition_use` (`:1449`),
   `scc_component_for_definition` (`:1481`), `scc_component_members` (`:1497`),
   internal/incoming-use helpers (`:1513`, `:1529`), and component queries
   (`:1562`, `:1577`) mutate Arc-backed atomic probes. Batch `counters()`
   (`:1538`) reads these atomics; finish includes that snapshot. A producer
   using these helpers changes counted behavior even if it mutates no rows.
   `ConstraintBatch` derives `Clone` (`:795`) and stores these probes as
   `Arc<AtomicUsize>` (`:845`): cloning the batch does not isolate counters.
   The private sealed-plan accessor (`:1969`) is uncounted; existing
   feature-gated topology observation (`:1343`) is also uncounted but is not
   authorization to add a production observer. Exact constructor access must
   be designed and checked, not inferred from `&self`.
2. **Discarding only metadata failures does not prove identical resource-state
   acceptance.** A sidecar reservation can succeed and retain a positive
   amount of storage before a later F5 fallible reservation. Under a resource
   state where that F5 reservation succeeds without the sidecar and fails with
   its retained allocation, the sidecar itself has not failed and its failure
   handler never discards it. `reserve_startup!` (`:9610`) propagates F5
   reservation failure, and public `solve` propagates it. The current API has
   no retry that drops metadata and restores the consumed batch/session.
   `ConstraintStore::with_capacity` (`:3142`) additionally uses infallible
   `Vec::with_capacity`/`HashMap::with_capacity`/`HashSet::with_capacity` and
   `Arc::new`. This is a structural counterexample to an unconditional
   unchanged-acceptance claim, not a measured failure frequency. The design
   needs an explicit interpretation/approval of added resource coexistence;
   isolation alone proves no change to F5 facts, not equal availability under
   all memory states.
3. **Successful finish is not a source semantic certificate.** The terminal
   construction (`:15970`) transfers only existing F5 output owners. No
   source-publication event, immutable-world law, authentic anchor formation,
   or complete inlet/event schema is supplied by this move. The absence of
   a metadata supplier cannot be repaired by accepting a successfully solved
   row or pretending a scheme-install event supplies it.
4. **Late metadata rejection is not rollback.** `run(self)` and `finish(self)`
   return only a result or copyable error, and consume the attempt. Even if
   an error is detected after closed finalization, no live session/batch is
   returned. A retained clone outside solve is a separate caller arrangement,
   not the existing solver's resumable failure behavior.
5. **Keeping counters identical is not complete resource accounting.**
   `ProductionCounters` (`:2130`) has no SourceBuild lanes; the resource
   sampler's inputs (`:10257` onward) and finish combination (`:15899`) describe
   existing F5 containers. A new private package may leave those legacy values
   unchanged while adding real live bytes and retaining owner dependencies.
   That must be accounted separately under the draft's phase sets; unchanged
   legacy counters do not prove unchanged total peak or retained storage.

## Missing premises and shared-record delta

Still missing: an approved failure disposition for each distinct outcome;
the exact error/reporting channel if any new failure is surfaced; the
definition of the unchanged-resource/acceptance claim; authentic supplier and
owner graph; fallible-allocation/teardown manifest; uncounted constructor
access; complete terminal lifetime/transfer argument. No existing compile
wrapper or `SolveError` supplier was found in the inspected scope.

Primary-owned delta: link this audit from the next id SourceBuild review
record; retain the producer/failure-policy gate as open; record the resource
coexistence counterexample and the counted-query isolation obligation in
`tasks/current.md` or the governing draft repair. Do not change aggregate
theorem statuses or select a failure arm based on this audit. No shared task,
design, index, or theory file was edited by this worker.

Inspection commands: `sha256sum` on the frozen draft; bounded `rg` symbol and
direct-caller searches (including one no-ignore search for compile/error names);
`sed`/`cat` source and governing-rule reads. No test/build/measurement command,
Git operation, or compiler edit was performed. Source locators and the policy
table are static evidence; allocation probabilities, panic deployment profile,
user-facing rendering, and executable isolation remain unverified.
