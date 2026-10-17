# Sprint ordinary-hir-applied-conformance-repair-20261017

Status: APPLIED REVIEW IN PROGRESS; TEST-ADAPTATION AMENDMENT. Revision
6 supersedes revision 5 only for the one test-only compile repair, one explicit
post-repair unit invocation, integration caps and remaining resource allocation.
Revision 4 remains authoritative for semantics and implementation.
Candidate baseline
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
   **Completed CLEAN:** `notes/progress/2026-10-17-ordinary-hir-repair-architect-review.md`,
   SHA-256 `635cd68b611d652f4d6760026888945518423b8be69729560418807d9fbbc339`.
   Luna authorizes the private `lib.rs` provenance seam and the exact expanded
   implementation lease below; this is not implementation evidence or theorem
   closure.
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
   **Compiler review completed with one MINOR only:**
   `notes/progress/2026-10-17-ordinary-hir-repair-applied-compiler-review.md`,
   SHA-256 `2395d3ca4abd65b5c4a530f691cef5cb0b4688e8ec91913b255c48625b117191`.
   It found `append_stage` preceding owner-slot/root validation and checked
   counter increment. Luna grants a single narrow repair of `module.rs` and
   the existing handoff, cap 30s, then a fresh independent compiler delta
   review of this ordering only, cap 30s. Both are charged from the 120s
   reserve, leaving reserve 60s. Preserve the candidate and its review receipt
   at commit `5d9ecdfff`; do not modify other code/test paths. The repaired
   ordering must validate item index, binding kind, exact empty-error
   placeholder/root, and counter increment before `append_stage`; replacement
   after merge must have no remaining fallible validation or arithmetic.
   If either 30s cap is exhausted without frozen acceptable evidence, STOP and
   hold execution; do not consume more reserve.
6. Spec review found that the two integration targets do not execute three
   private `module.rs` unit falsifiers: conflicting root mapping at line 3078,
   final `evaluation_class` at line 3160, and 64 indexed finalizations at line
   3182. Rev5 added a focused unit command and all required reviews were CLEAN.
   Its first invocation ran once but failed before test discovery (exit101,
   2.67s): `lib.rs:2611` matched `HirExpr::Error` against `AssociatedExpr` in a
   `#[cfg(test)]` assertion. Exact log:
   `notes/progress/2026-10-17-ordinary-hir-repair-unit-run-failure.md`.
   Therefore no test ran. The two integration commands were not started.

   Rev6 explicitly authorizes one narrow test-only repair: in that assertion,
   match `expression.hir` while preserving the exact expected `HirExpr::Error`
   structure. The Luna/high implementer may edit only
   `crates/yu-hir/src/lib.rs` and the existing implementation handoff, cap30s.
   No other code/test/expectation changes are authorized. After STOP, freeze
   hashes and obtain a fresh compiler delta review of this exact edit and
   unchanged assertion meaning, cap30s. If the repair or review cap is exhausted,
   STOP; no execution follows.

   After CLEAN delta review/adjudication, Luna may invoke the unchanged focused
   command exactly once after repair (this is one explicitly amended invocation,
   not a retry allowance):
   `cargo test -p yu-hir --features shadow --lib module::tests::` (<=45s).
   If it succeeds and discovery includes the root-collision,
   final-classification and 64-item falsifiers, run each remaining command
   exactly once, sequentially:
   `cargo test -p yu-hir --features shadow --test ordinary_application_admission`
   (<=90s), then
   `cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical`
   (<=90s). The first failed invocation is preserved; no further unit invocation
   is authorized. Any further timeout, compile failure, missing falsifier or
   assertion failure stops all later commands with no retry, substitution or
   expectation edit. A fresh post-run regression review <=90s checks the exact
   receipt whether execution stops early or completes. The assertions close only
   the execution-coverage finding; they close no original theorem condition.

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
plan and shared handoff. Cargo execution configuration is frozen at:

```text
Cargo.toml                  d61446115ce45d7010898090bce323fe1134b1cca53471ac9416e441d45865d9
Cargo.lock                  2055b82e7c2c68df727940d7053da0490368a99217bd3587866a7003177484e6
crates/yu-hir/Cargo.toml    a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1
crates/yu-solver/Cargo.toml 7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c
```
The original `5fbceb68d` table below is historical baseline evidence only; it is not the implementation input manifest.

Baseline pins from `5fbceb68d`:

```text
crates/yu-hir/src/module.rs                                      2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/source_identity.rs                              aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
crates/yu-hir/src/shadow.rs                                       2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
crates/yu-solver/tests/research_accepted_call_vertical.rs         78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963
```

Fresh cap: 2760s. Through the first unit-command compile failure, 2352s are
charged. Remaining 408s are allocated: narrow repair author30; compiler delta
review30; one post-repair unit invocation45; first integration90; second
integration90; post-run regression review90; contract/adjudication coordination
15; reserve18. These sums include all explicit command caps; no retry or implicit
command is funded. No retired budget carries. Preserve all three inherited
UNKNOWN writer leases and their reservations. At most one author at a time;
proof, plan, architect, implementation and reviews are sequential.

Stop at another counterexample, hash/pin mismatch, grammar breach, unreviewed
identity representation, source owner outside exact leases, unaccounted
superlinear work in V/E/R, or exhaustion. Do not alter the adopted source
semantics or resource amendment. No production promotion.

Closeout reports only original conditions closed, newly established compiler
behavior, and the exact remaining unproved condition/next cut.
