# Sprint ordinary-hir-applied-conformance-repair-20261017

Status: PLAN FROZEN; AWAITING PRE-CODE ARCHITECT REVIEW. Revision 2 supersedes
revision 1 for the live dependency/lease sequence. Candidate baseline
`4f4dcb7b9`; current operational base may include later record-only commits.
The prior sprint closed `REVIEWED-PARTIAL`; its candidate and
exact compiler findings remain immutable:

- Candidate: commit `4f4dcb7b9`.
- Review: `notes/progress/2026-10-17-ordinary-hir-applied-compiler-review.md`,
  SHA-256 `9f576d7f6362f87ae21d01d997dc7418c529aade689d7eafbd22d78b5cf239a6`.
- User-adopted semantics: rev4 SHA-256
  `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
- User-adopted resource replacement: amendment SHA-256
  `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e` and
  adoption receipt SHA-256
  `bcbc089b62315bf38288e179ef992c7658a5a68a8054ce669258ec474a42b388`.

## Parent and single outcome

Parent is the original Yulang inference/execution theorem. Preserve original
Simple-sub A/B claims, quantifiers, source domain and source/native
correspondence; F1/FK1, N-Transport, Call, soundness, principality, termination
and production remain OPEN. Original theorem conditions discharged: 0.

Single outcome: repair the frozen ordinary-HIR admission candidate so its
implementation is ownership-correct, matches the adopted Atom/Group/Apply
source grammar and retained diagnostic order, preserves final binding
classification and authentic source-key ownership, has only O(V+E+R) projection
work/storage (excluding stated existing module/carrier passes), and is covered
by exact regressions plus a vertical ordinary-lowering candidate observation.
No semantic Call rule, solver production semantics, theorem-quantifier change,
source narrowing or public representation change is in scope.

The seven exact findings are listed in the linked compiler-review receipt.
Each must be closed with a named repair and falsifying regression, including a
many-simple-bindings discriminator for root lookup complexity. R counts all
physically stored flat Apply error-ID references, including repeated ancestor
references. Each Apply list is materialized once; Group forwards without list
cloning. Checked child/R/byte/ordinal arithmetic and fallible reservations must
precede publication; no partial module/list or duplicate/truncated diagnostic.

## Sequence and leases

1. Sol/high proof/source producer <=240s, writing only:
   - `notes/theory/2026-10-17-ordinary-hir-applied-repair-invariants.md`
   - `tasks/agent-loop/inbox/20261017-ordinary-hir-applied-repair-invariants.md`
   Derive authentic node/key ownership without range-based reconstruction;
   preserve atom error events at the prior scheduling point; classification is
   determined by final canonical expression. Pin actual source constructors,
   association implementation, carrier boundary, error sink and all seven
   counterexamples. Do not edit code. STOP/freeze.
   **Completed:** worker `/root/ordinary_hir_repair_invariants` STOPPED with
   frozen theory SHA-256
   `1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28` and
   handoff SHA-256
   `7bd7cfe427f498c88bab2fab71ae1f24b4ab7f30c24552bbd2030404dcbdf6c3`.
   Exact elapsed UNKNOWN; charge full 240s reservation. No implementation or
   tests ran.
2. Luna authors a narrow implementation plan <=90s, then STOP/freeze:
   - `notes/design/2026-10-17-ordinary-hir-applied-repair-plan.md`
   - `tasks/agent-loop/inbox/20261017-ordinary-hir-applied-repair.md`
   **Completed:** frozen plan SHA-256
   `45c4cebfc6b5f35cf2f081db61959558721757f6a3a3f802ae310181f5ea4dc3`; see
   the shared handoff for exact source pins and feasibility questions.
3. Fresh architect <=120s reviews only authentic provenance feasibility,
   public-surface preservation, association allocation/resource accounting,
   staging/order, linear root indexing and the proposed exact source-owner
   lease. The proposed source seam is crate-private and construction-owned in
   `lib.rs`; public `HirExpr` remains unchanged. If this cannot be implemented
   without a public representation change, second association walk, unleased
   owner or unsupported resource claim, STOP before edits and name the exact
   boundary. Luna adjudicates the frozen result.
4. Only after CLEAN architecture review and Luna adjudication, Luna/high
   implementer <=1110s may write only:
   - `crates/yu-hir/src/lib.rs` (newly added: private provenance seam only)
   - `crates/yu-hir/src/module.rs`
   - `crates/yu-hir/src/source_identity.rs`
   - `crates/yu-hir/src/shadow.rs`
   - `crates/yu-hir/tests/ordinary_application_admission.rs`
   - `crates/yu-solver/tests/research_accepted_call_vertical.rs`
   - `tasks/agent-loop/inbox/20261017-ordinary-hir-applied-repair.md`
5. After STOP/freeze, sequential fresh applied reviews: compiler <=180s,
   spec <=120s, architect <=180s. Then regression pre-run <=120s.
6. Only after all CLEAN, one primary owner runs each command exactly once,
   sequentially, maximum120s each:
   `cargo test -p yu-hir --features shadow --test ordinary_application_admission`
   `cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical`
   A fresh regression reviewer <=120s checks the post-run receipt. No implicit
   retries or edits to expectations.

The vertical may establish ordinary lowering, authentic HIR source ownership,
CandidateInference, propagation, exported definitions and candidate source
observations only where the existing feature-gated API provides them. The first
standard consumer `ConstraintBatch::collect`/`collect_mode` still returns Error
for Apply/Group and records `ApplicationTypingRuleUnresolved`; keep it OPEN.
This sprint supplies no standard Call typing, source T, native adequacy or
parent theorem result.

## Pins, resources and stop

The current-input pin for newly proposed `lib.rs` is
`5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464`. Exact
current candidate pins and frozen proof outputs are listed in the frozen Luna
plan and shared handoff. The original `5fbceb68d` table below is historical
baseline evidence only; it is not the implementation input manifest.

Baseline pins from `5fbceb68d`:

```text
crates/yu-hir/src/module.rs                                      2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/source_identity.rs                              aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
crates/yu-hir/src/shadow.rs                                       2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
crates/yu-solver/tests/research_accepted_call_vertical.rs         78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963
```

Fresh cap 2760s: coordination120; proof/source240; Luna plan90; pre-code
architect120; implementation1110; applied reviews480; pre/post regression240;
Cargo240; reserve120. Total 2760. No retired budget carries. Preserve all three
inherited UNKNOWN writer leases and their reservations. At most one author at a
time; proof, plan, architect, implementation and reviews are sequential.

Stop at another counterexample, hash/pin mismatch, grammar breach, unreviewed
identity representation, source owner outside exact leases, unaccounted
superlinear work in V/E/R, or exhaustion. Do not alter the adopted source
semantics or resource amendment. No production promotion.

Closeout reports only original conditions closed, newly established compiler
behavior, and the exact remaining unproved condition/next cut.
