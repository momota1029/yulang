# Frozen handoff: Catch source/export observation

Sprint: `source-matched-catch-action-and-export-20261017`, contract rev3,
SHA-256 `2127068d4b5d7c90f11ed7306f1f381226d5d8464b111eac07a19fabf72f7d07`.
Assignment: `assignment-catch-source-export-20261017`.
Status: implementation artifact frozen; execution and source observations remain
UNKNOWN until Luna's sole authorized Cargo example attempt after review of these
frozen bytes. This handoff is unreviewed and grants no theorem or production
authority.

Worker/runtime: `/root/catch_source_export`; opaque session ID UNKNOWN; current
collaboration task is the runtime receipt. Requested model/effort: gpt-6-luna /
high. Observed model/effort: UNKNOWN / UNKNOWN. Active-work acknowledgement was
sent to Luna before any write. No descendants or coauthors.

## Source and intended observation

The example contains the pinned existing test literal exactly: 138 bytes,
SHA-256 `9a86d2e0d0004cbdbd4be96dcdc284b6648287a203518c93211c43705f8ed8d3`.
It lowers that source through `parse_file` and
`lower_module_with_local_source`, authenticates parse-owned definition,
declaration, occurrence and binder/use keys, and invokes ordinary
`CandidateInference::solve`. It requires `observes_hir` and zero candidate
conflicts before calling the borrowed `source_call`, `fresh_use`, and export
APIs. Export attempts use the actual HIR-owned `id` and `result`
`DefinitionRootId`s. `fresh_use(None)` is printed as `result=None`.

Expected source inventory checked by the example: the declared `signal::ping`
operation and its scrutinee/pattern incidences, `id` and `result` roots/source
keys, `id` parameter and use, Catch `k` and `v` binder/use links, and three
retained Apply source occurrences. The example associates observations only by
exact occurrence and source-key agreement. It does not synthesize a source
identity or route.

No runtime result is claimed yet. If source/HIR authentication differs, solve
fails, conflicts are present, or a public observation cannot be tied to the
exact source occurrence, stop at that stage. Exports are withheld before the
zero-conflict gate. The one allowed Cargo attempt belongs to Luna and is capped
at 120 seconds; a failure consumes it, with no retry or source simplification.

## Parent and semantic boundary

The proof input is frozen in
`notes/theory/2026-10-17-source-matched-catch-actions.md` (SHA-256
`064e813a0bcf82019d9379dfa25fd1c825eabd2072c5933f32b28d6d1ea284ae`) and its
handoff (SHA-256
`61a5b4d5487871cb474e79148ac835dfaf01075ff3a54ef673cb71d02f9e6fda`). It
constructs source-matched selected-request and normal-completion actions for
the literal, then leaves the exact premise
`CATCH-SPECIMEN-TYPED-INCIDENCE` open: complete typed handler-exit/matcher and
response-entry/callback/parent composition is not supplied by the static
source/native records.

Even if the example succeeds, it demonstrates only that the exact source/HIR
artifact traversed these candidate constructors and borrowed APIs. It does not
establish handler semantic adequacy, full source typing, detached/publication
export, runtime execution, F1/FK1 or another parent obligation. The result stays
observational and provisional. Falsifiers are the exact contract conditions:
literal/declaration/occurrence/root mismatch, a fabricated or foreign root,
solve bypass, conflict bypass, or an unexplained source_call/fresh_use
association. Luna owns cleanup/removal of this research example if the
observation is falsified or the research use ends; no library/compiler cleanup
is implicated because no library path changed.

## Evidence, reuse and limits

Inspected and reused: the source-authentication flow in
`crates/yu-solver/examples/research_source_registration.rs`; exact specimen and
provisional Catch cases in `crates/yu-solver/tests/candidate_operation_catch.rs`;
the HIR LocalSource/declaration provenance owners; ordinary
`CandidateInference::solve`, its HIR/conflict gates, and public borrowed
`source_call`, `fresh_use`, and conflict-gated `export` implementations. The
proof artifact's exact missing incidence is preserved.

Rejected as evidence: prior fixture's assertion as a fresh run; candidate
conflict-free output as source typing or handler adequacy; a borrowed graph as
detached export; any assumption that `fresh_use` must exist; source simplification
or a semantic interpretation of provenance.

Static checks only: rev3 contract hash, all 46 direct dependency hashes, both
proof artifact hashes, exact literal/length/hash comparison against the pinned
test, and leased-output byte hashes at freeze. No build, test, Cargo run, Git
operation, library edit, fixture/expectation change, scratch/generated file, or
independent review was performed by this worker. Runtime and export outcomes are
left for the single primary attempt.

## Artifacts, budget and stop

Exact implementation leases, exhaustive:

1. `crates/yu-solver/examples/research_catch_source_export.rs` — new research
   example; SHA-256 recorded to Luna at freeze.
2. `tasks/agent-loop/inbox/20261017-catch-source-export.md` — this handoff;
   its byte hash is sent to Luna separately to avoid a self-hash cycle.

`notes/progress/2026-10-17-catch-source-export.md` is primary-only and was not
written by this worker. No other path, scratch output, generated artifact or
disposable file was created. Five-stage maximum; implementation budget 480s.
Active-time instrumentation is unavailable, so charge the full 480s
conservatively; remaining budget is zero. Work stages: pinned-input and owner
inspection; source/HIR identity example; public candidate observation and
gating; handoff and freeze audit. Worker state: STOPPED after the frozen bytes
and hash notification. No outstanding descendants or writer lease remains.

Next in-envelope step: Luna reviews these immutable bytes, then may spend the
single <=120s Cargo attempt and record its exact outcome in the primary-owned
progress path. A fresh independent `regression_auditor` review is required;
the author cannot certify this result.
