# Sprint R149 — unchanged Yulang2 Types and Console execution

Status: CANDIDATE; not active, no workers or leases granted
Branch / baseline commit: `research/simple-sub-intrusion` / `aa6341391`
Authority: Reviewed Draft at `notes/design/2026-10-20-r149-types-console.md`;
proof plan at `notes/theory/2026-10-20-r149-types-console.md`.
Both require explicit user approval before semantic implementation.
Contract revision: rev1 candidate; SHA-256 recorded after prospective review.

## Original outcome and success evidence

Original outcome: proof-backed Yulang inference and evaluator behavior that
runs unchanged Yulang2 Web examples as broadly as practical. This sprint
targets the exact pinned `Types` and `Console` templates as a shared-path
increment. It does not redefine the goal as only these two examples.

Original parent obligations: Simple-sub/evaluator A/B, R70/R71, source/native
correspondence, soundness, principality, and production admission remain OPEN.
This sprint supplies finite source-to-runtime evidence; it does not close
those general claims or authorize a production cutover.

Exact source and outputs are pinned in the Reviewed Draft. Success requires
the complete 142-byte and 92-byte source templates unchanged, accepted public
types for `id`, `answer`, `name`, and `pair`, Types output separated from
execution values, and exact ordered host-write payloads. CLI and Web consume
the same accepted module/HIR and actual pinned standard-library definitions.
The Types payload is `(42, Yulang)\n`; Console payloads are
`hello from Yulang\n` then `3\n`.

Before/after evidence: currently there is no standard library in this Y3 tree;
`yu-types` has no tuple node; the playground exposes only selected-definition
execution; `run` rejects unhandled requests. After the sprint, the two pinned
examples must pass the contracted CLI and Web checks, with proof/review receipts
for tuple type construction, authentic library resolution, mixed module order,
host request continuation, and atomic publication.

Known prerequisites: user approval of the Reviewed Draft; exact source-owner
map for tuple syntax/HIR/type/solver and standard-library resolution; an
identity-bound host response path for `out::write`; a module entrypoint that
does not invent a selected definition while preserving the existing mixed
source schedule. R148's 120 seconds do not carry forward.

Non-goals: changing either Y2 source or expected output; spelling-based
intrinsics for `say`, `println`, `show`, or `out::write`; suppressing effects;
rewriting module expressions as `main`; claiming general Y2 compatibility or
closing any parent proof/adoption gate.

## Two continuing lanes

Proof lane (only after activation): a `prover` constructs one identity-preserving
chain from pinned source/HIR through tuple and library constraints, accepted
inference, actual runtime schedule, identity-authorized host response, and
ordered output; each useful result is applied to the finite source obligation.
Falsifiers include reordered/collapsed tuple components, untrusted primitive
leaves, executing a different HIR/library set, skipped computation initializers,
duplicate or forged writes, and partial publication. A fresh compiler/source
reviewer who did not author the proof certifies the frozen chain.

Complementary source attack: Luna checks the pinned Y2 constructors/consumers
and searches for counterexamples to module order, polymorphic element
instantiation, method selection and continuation ownership. This lane is not
self-review of the proof author.

Implementation lane: Luna grants an `implementer` exact per-file leases only
after the user approves the design and a prospective reviewer confirms the
source-owner map. Required path families are `crates/yu-syntax/`,
`crates/yu-hir/`, `crates/yu-types/`, `crates/yu-solver/`,
`tools/inference-playground/`, `apps/yulang-wasm/`, `web/playground/`, plus
finite tests/fixtures and vendored pinned stdlib sources. These are planning
families, not current leases. Activation must replace them with an explicit
nonoverlapping file list and exact hashes. Production promotion remains
unauthorized while parent gates remain OPEN.

Both lanes are intended to progress in parallel after activation. A proof
obstruction does not stop independent implementation whose semantics are
authoritative. A semantic/source contradiction returns to Luna; workers cannot
revise this contract, add paths or claim authority. No Astra assignment is
proposed: no named risk currently justifies the resource.

## Permissions and resources

No current permissions or write leases are granted. Before activation, Luna
must record the exact file map, full clean baseline/tree identity, direct
dependency hashes, oracle checkout/commit/blob owners, proof and implementation
handoff paths, and independent reviewer assignments. Unknown writers retain
quarantined paths; this candidate does not release the board quarantine or R104
lease.

Proposed fresh cap: 3,000 seconds, Astra 0, no carryover. Planning estimate:
authority/owner map 240s; prospective review 240s; implementation 900s; proof
600s; CLI/Web checks 360s; independent final reviews 360s; closeout 300s.
The primary charges each full reservation when issued and stops at the cap.
The proposed cap starts only if the primary activates R149 after user approval.
Earlier primary design research/reviews happened before an R149 reservation
existed and are not recorded as sprint charges. On activation, the fresh cap
includes owner mapping and prospective review before any code lease; inactive
proof, implementation and execution remain unstarted. No R148 allocation
carries over.

Proposed verification seam after implementation freeze:

```sh
cargo test -p yu-hir --features shadow
cargo test -p yu-types
cargo test -p yu-solver --features shadow-apply-candidate
cargo test -p yu-playground
cargo test -p yulang-wasm
npm --prefix web/playground run typecheck
npm --prefix web/playground run check
```

The Web check builds WASM and the page, then runs `smoke-test.mjs`. Run one
heavy Cargo/build process at a time and keep all scratch/build outputs under
their exact owner. The solver and HIR commands include the candidate/shadow
features that compile the paths under review. Existing package checks alone
are insufficient for success: after approval, add
`tools/inference-playground/tests/yulang2_types_console.rs`, exact unchanged
fixtures under `web/playground/examples/`, and assertions in
`web/playground/smoke-test.mjs` for both fixture byte identities, accepted
public type names/schemes, Types UI output, exact host payloads, write order,
and failure withholding. The CLI integration and WASM smoke path must execute
those exact fixtures without rewriting or injecting `main`. Freeze the test and
fixture paths and hashes in the activated revision. Tests establish finite
behavior only; they do not prove the parent theorems.

Stop on missing user approval, unlisted source owner/dependency, unsupported
runtime operation, source rewrite, output/order mismatch, failed source/native
identity, partial publication, independent-review blocker, confirmed STOP, or
budget exhaustion. Unknown runtime/worker cessation retains its reservation and
lease. Session end leaves no worker recorded RUNNING without current runtime
evidence.

## Frozen seams and handoff

The candidate design and proof plan are the current immutable reviewed seams;
the candidate sprint contract is not yet reviewed or active. On approval, freeze
the revised contract and all direct dependencies, allocate one proof handoff and
one implementation handoff, then obtain fresh prospective spec and
compiler/source review before granting any code lease.

The proof lane must keep finite witness claims distinct from R70/R71, A/B,
soundness, principality, and production readiness. The implementation lane
must connect the same source identity through solver acceptance, schedule
construction, host continuation response, CLI and Web output. Luna alone
adjudicates results and performs explicit-path staging, commit and push.

Current scheduling state remains R148 `ENDED` and `CLOSED_UNFINISHED_RESEARCH`.
This candidate does not modify `tasks/agent-loop/current.json`, start workers,
assign leases, or begin semantic work. If approved, the next material dispatcher
boundary is sprint activation after owner/dependency freeze and prospective
review.
