# R30 native mapping: candidate source-context guard interpretation

Status: research-only source/native correspondence; no implementation or
production claim. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`
remains OPEN/closure0. Candidate guard definition:
`notes/design/2026-10-18-source-context-guard-interpretation.md`, SHA-256
`ec09c5281f172aac38fb17adf835f248564b64acf6b0e58ab62949c042127a76`.
R30 contract SHA-256
`33a22c367d24a53329a7fb8adcd9e2408d86cdcfedee64b8773fa8072c4e4913`.

## Constructor-to-consumer map

| Candidate field | Nearest current source/native owner | Current evidence and missing input/consumer |
| --- | --- | --- |
| `registry: ResolvedRegistry(P,M;xi)` | `tools/inference-playground/src/lib.rs::prepare`; `yu_hir::module::lower_module_with_counters`; `source_annotation::declarations` | HIR retains source module, family/member keys, declaration visibility and parsed signatures. The selected caller supplies no predecessor `P`, old registry/evidence, `xi` or dependent merge action. |
| `scope: ResolvedScope(P,M,theta0;xi)` | HIR source/binder identities and `SourceOperationDeclaration` name/signature positions | Exact syntax identities and local resolution are retained. No caller's original joint `theta0`/scope witnesses or old/new dependent scope action enter the selected path. |
| `authority_known: SourceVisibleCurrent(P,M,e0;xi)` | Declaration visibility and runtime `owner_active`/handler installation checks | Visibility is static. Runtime activity is checked later at operation/handler execution and does not supply the original `e0` current-authority witness. No consumer joins visibility with the original authority predicate. |
| `incidence_known: ExactTypedIncidence(P,M,C0,e0;xi)` | Typed-boundary semantic relation; runtime request/receipt events in the operation-v1 research route | HIR source references do not construct the exact `Path` flow + `Observe` + same-view receipt at the original event, or activity of `h`, `owner(h)` and `b.receiver` at `C0`. The specialized runtime receipt is later and belongs to another scenario. |
| `old_frame`, `global_residual`, `authority_residual`, `incidence_residual` | `SemanticImports::with_caller_evidence` is the only caller-payload retention seam found | It checks parse root, exact source declaration and module identity, then retains opaque data. It does not validate the dependent types, retraction, global predicate equivalence, or original guard semantics. Candidate solver has no consumer. |
| `alias_projection`, `capture_projection`, `shared_equalities`, `overlap_frame`, alias/capture/shared residuals | Source syntax/binder IDs and HIR local-source reference resolution | Syntax can identify references and lexical binders. No native mapping supplies all semantic witnesses under original `theta0`, arbitrary old/private/shared overlaps, or proof that aliases/captures agree at original scopes. |
| Original `j0/a0` readout | No consumer on `CandidateInference::solve_mode` / `InferenceSession` path | Solver consumes HIR and generated constraints. No interface accepts or projects these original dependent guards. Candidate acceptance is not a `PhiW` guard consumer. |
| Same-root `Z.V/Z.Car` certificates and fixed-`c` license | Existing proof schemas and separate Operation constructor audits | These are distinct original obligations. This mapping locates no producer for either at selected caller; source signatures/solver candidate do not manufacture them. |

## Caller and runtime timing

`prepare` accepts source text, module name and scoped-mode flag; it parses and
lowers using `SemanticImports::empty()`, then solves candidate inference.
`execute` completes that preparation/inference before it constructs a
`RuntimeProgram` and starts the source schedule. Runtime `ModuleRun` is a
source-execution state with empty active receiver state at entry. It is not a
pure context-forming action at the original `(C0,w0,e0;xi)`. Moving execution
before inference conflicts with the adopted top-level inference principle.

This means the nearest API seam can retain opaque evidence but cannot mint or
consume a validated candidate interpretation. Adding the R30 record to HIR
would be transport only; solver use of a record-shaped payload would still
need independent constructors, typed projections, and the frame proof.

## Result

**NO_SAFE_CODE_SLICE** for source-context guard construction or use in the
inspected selected route. Every candidate field either has only structural
source identity, has no source/native constructor at the original event, or
is explicitly an unresolved residual. No opaque adapter, Boolean receipt,
test, or code edit is proposed. The prior R29 audit remains applicable to
unchanged source bytes. A later implementation lease requires a reviewed
interpretation whose actual independent field inputs and semantic consumer
exist at matching indices.
