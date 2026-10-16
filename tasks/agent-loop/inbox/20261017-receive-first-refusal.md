# Frozen implementation handoff

Sprint-ID / contract revision and SHA-256: `receive-negative-row-and-refusal-cut-20261017` / revision 3 / `b22e10ff89c4221a1562cf2275530ba626635d072760ed6160a4509b479f283a`

Assignment-ID / handoff revision: `assignment-receive-first-refusal-instrumentation-20261017` / 1

Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2`, exact fixture `tasks/agent-loop/fixtures/20261017-receive-choose.yu`; identify only the first existing `CandidateInference` refusal for the frozen bytes. This does not establish source acceptance or close any parent theorem.

Baseline / direct dependency hashes: baseline `cba9d794d1f0498262b3668f9d5cc055c16749e9`; the proof artifact `notes/theory/2026-10-17-receive-negative-row-source-judgment.md` is pinned at `3b24b17bfd8cec91e0182b1f417516bc9b6ad78aa248d3af108454c077ab33fb`, and its handoff at `ed6df4086c8a968b9ce9a53a8db5b1db4c6a3d513cb706a43605c0ac7e6581e4`. The two edited files matched Luna's pre-edit snapshots before writing: `shadow_apply.rs` `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`; `candidate_source.rs` `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.

Role / actual worker / session / launch or resume receipt: implementer / `/root/receive_first_refusal_instrumentation` / current session / active-work acknowledgement sent to Luna before edits. Descendants: none.

Requested model and effort / observed model and effort: `gpt-6-luna` / high; UNKNOWN / UNKNOWN (runtime metadata not exposed).

Exact leased paths / authors: `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/candidate_source.rs`, and this handoff only. Author: `/root/receive_first_refusal_instrumentation`; no other contributors.

Outcome class: provisional instrumentation.

## Outcome and parent application

Added temporary, uniquely named stderr branch labels immediately before existing `CandidateError::Unsupported` returns or propagation points in the candidate preflight path. The labels make a later primary-owned run identify which existing refusal is first. Candidate-source preflight is reached before placeholder-error retention and before source actions proceed. No run was made in this lane, so the actual first refusal remains unknown and no source-to-constraints acceptance or execution path was observed.

No branch predicate or order, return value, public API, fixture byte, annotation domain, candidate admission rule, inference behavior, diagnostic expectation, or source semantics was intentionally changed. In shared `preflight_expression`, markers are gated on `calls.is_none()`, the `CandidateInference::solve_mode` call mode; the other caller's call-inventory mode receives no marker.

## Marker inventory

Every marker is directly before the original refusal's `return Err(CandidateError::Unsupported)` or its original error propagation (`?`). The original return/propagation was not moved; the marker only names that branch.

| Marker | Site | Why this is the first branch label there |
| --- | --- | --- |
| `candidate_source::preflight.source-annotation` | `candidate_source.rs:410` | Immediately precedes the existing source annotation preflight refusal. |
| `candidate_source::preflight.binding-annotation` | `candidate_source.rs:415` | Immediately precedes the existing local binding annotation refusal. |
| `candidate_source::preflight.ascription-annotation` | `candidate_source.rs:422` | Immediately precedes the existing ascription annotation refusal. |
| `candidate_source::preflight.lambda-formal-annotation` | `candidate_source.rs:428` | Immediately precedes the existing formal annotation refusal, including the nested negative concrete row guard. |
| `candidate_source::preflight.operation-signature` | `candidate_source.rs:436` | Immediately precedes the existing operation signature match fallback. |
| `candidate_source::preflight.catch-signature` | `candidate_source.rs:451` | Immediately precedes the existing catch signature match fallback. |
| `candidate_source::preflight.unresolved-name` | `candidate_source.rs:459` | Immediately precedes the existing unresolved or ambiguous name refusal. |
| `shadow_apply::solve_mode.item-shape` | `shadow_apply.rs:301` | Immediately precedes the existing unsupported top-level item fallback. |
| `shadow_apply::solve_mode.hir-errors` | `shadow_apply.rs:311` | Immediately precedes the existing remaining-HIR-error refusal. |
| `shadow_apply::solve_mode.scoped-scc-use` | `shadow_apply.rs:317` | Immediately precedes the existing scoped SCC-use refusal. |
| `shadow_apply::preflight_expression.initial-reserve` | `shadow_apply.rs:1051` | Emitted in the existing reserve error mapper, before `?` propagates its original `Unsupported`. |
| `shadow_apply::preflight_expression.depth-limit` | `shadow_apply.rs:1064` | Immediately precedes the existing depth-limit return. |
| `shadow_apply::preflight_expression.pending-reserve` | `shadow_apply.rs:1072` | Emitted in the existing reserve error mapper, before `?` propagates its original `Unsupported`. |
| `shadow_apply::preflight_expression.permitted-errors-reserve` | `shadow_apply.rs:1098` | Emitted in the existing reserve error mapper, before `?` propagates its original `Unsupported`. |
| `shadow_apply::preflight_expression.formals-reserve` | `shadow_apply.rs:1122` | Emitted in the existing reserve error mapper, before `?` propagates its original `Unsupported`. |
| `shadow_apply::preflight_expression.expression-shape` | `shadow_apply.rs:1132` | Immediately precedes the existing unsupported expression fallback. |

## Evidence, checks, and boundaries

Prior evidence reused: the reviewed source-authentication correspondence and its clean review receipt, which predicted negative formal preflight before placeholder retention; the prior run receipt, which recorded only generic `Unsupported` at candidate solve; and the pinned source judgment, which identifies the nested negative `[ctrl]` formal but leaves its paired source construction/transport premise open. Those records do not report this run's branch.

Owner/source inspection included `CandidateInference::solve_mode`, `candidate_source::preflight`, and the shared `preflight_expression`; relevant in-file preflight tests were inspected but not run. Rejected as evidence: the prior generic refusal as an exact branch trace, the proof prediction as a runtime observation, and any inference of source acceptance from the markers.

Focused checks performed: reviewed the two-file diff and verified both pinned pre-edit hashes before edits. Final source hashes: `crates/yu-solver/src/shadow_apply.rs` `991fda3255b79d48b1d75613a00ea1cd6f76ba9b57d13079b9018a5ebfd965bc`; `crates/yu-solver/src/candidate_source.rs` `f63b20a676e1c8b952b9fcda7872f7e6c461bb881882209063041244b955bc43`.

No tests, builds, Cargo invocation, probes, or compiler execution. Conservative active-time charge: full 420-second assignment cap because active time was not continuously instrumented; no remaining assignment budget. No dependency changed. No generated or scratch paths were created.

Provisional boundary / falsifier / cleanup owner: branch labels are temporary observational instrumentation only. Any evidence that a marker alters branch order, refusal/result, candidate behavior, or fixture bytes falsifies the instrumentation claim. Luna owns the single run (at most 120 seconds), exact restoration from both pinned snapshots, restoration hash verification, and cleanup; author-side source files are frozen now.

Next related step inside the envelope: Luna may perform exactly the one authorized Cargo invocation after acknowledging this frozen handoff, then restore both snapshots immediately. This handoff does not close `CHOOSE-SOURCE-2`; the exact negative paired interface and its transport/consumer through the returned value and local `g` use remain the proof/source-owned TODO.

Worker state / writes stopped: STOPPED; all three leased paths are frozen; no descendants or unresolved writer leases.

Review/integration: pending sequential fresh regression review after the primary run and exact snapshot restoration. No commit-ready production change.
