# Sprint R237 — gate-ready canonical literal generation proposal

Status: ADMITTED, primary-owned mathematical proposal preparation.
Baseline: `ed75110c7816f2e8be7adb6ca02cd949222f2a3a` on `yulang3`.
Original parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`. Goal remains the
whole Yulang inference guarantees; no source domain or quantifier changes.

## Outcome

Prepare one reviewable candidate equation for the original literal source
constructor. Include canonical type/value, intrinsic empty effect, pure Return,
original source ports and occurrence/root/event/scope/shared-witness
association; connect it to the actual symbolic `Build` consumer and show the
exact proposed literal induction use in the unchanged soundness root. Separate
syntax-fixed data from facts that would need to hold for every arbitrary
satisfying assignment. Preserve annotation, checking, conversion and enclosing
context obligations. Mark any all-eight direct-generation clause as a proposal,
not adopted algorithm authority.

## Authority and evidence

- Adopted L1 (`notes/design/2026-11-02-literal-l1-adoption.md`) authorizes the
  original eight payload/type/value introductions, original `(q,r,e₀,ξ,ω)`,
  empty intrinsic effect and pure Return. It explicitly does not supply a
  Simple-sub generator clause or solution readout.
- Top-level principles (`notes/design/2026-10-11-yulang-inference-top-level-principles.md`)
  require source type/constraint construction before propagation and prohibit
  special solving at generation. They do not select an all-eight direct
  constant equation.
- The pinned Simple-sub reference directly returns the canonical type only
  for integer literals. Typed-core §6's literal row is draft material without
  implementation authority. Conditional structural-shadow notes do not
  authorize the full effectful model.
- R236 proves the payload/type/value table, supplied-coordinate preservation
  and connection to R196's original symbolic `Build` formula; its fresh review
  blocks promotion of the all-eight generator equation.

## Exact leases and lanes

Primary Luna owns this contract, the proposal
`notes/design/2026-11-02-canonical-literal-generation-proposal.md`, current
state and the review receipt
`tasks/agent-loop/inbox/canonical-literal-generation-proposal-review.md`.
One fresh nonauthor `spec_auditor` reviews the frozen proposal and these
authority boundaries. No proof worker or implementation worker is activated:
theorem construction remains blocked on the generation/readout correspondence;
implementation remains `NO_SAFE_CODE_SLICE` because
`crates/yu-solver/src/candidate_source.rs` and runtime `literal.rs` do not
provide original arbitrary-assignment semantics.

Primary preparation budget: at most 1,200 seconds. Independent review: at most
600 seconds. Zero Astra. No build, tests, Rust/Cargo, new environment,
worktree, target or cache. Preserve UNKNOWN/quarantined leases and unrelated
dirty files.

## Review gate and stop conditions

Reviewer determines whether each candidate equation is already entailed by an
authoritative source rule or would select new algorithm semantics. Falsify the
proposal if it drops a checking alternative; merges synthesis, written-target
and final-root ports; resets contextual effects; substitutes occurrence,
root/event, scope or shared witness; or uses a chosen typing/solver result to
define generated constraints. If direct all-eight generation is new authority,
stop before adoption or theorem promotion and ask the user about this exact
reviewed equation. Adoption alone does not close soundness.

Success is a source-reviewed, gate-ready proposal with exact remaining parent
premises and a scoped adoption question only if required. Parent-premise delta
is reported separately; no theorem/root closes in this planning/definition
packet.
