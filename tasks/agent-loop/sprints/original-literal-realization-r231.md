# Sprint R231 — original literal solution/readout at InferenceSoundness

Status: **ADMITTED WITH PROOF ACTIVATION GATE**. Branch `yulang3`; baseline
`c5cc9682aa2f4cb90a64d595202adc28ec570887`. R230 is closed and pushed.
Contract revision 1; primary Luna. The user resumed the unchanged
`research/simple-sub-intrusion` goal and authorized in-scope continuation and
Lean cache generation. Existing cache only; no new worktree, environment,
project copy, scratch cache or cache directory.

## Original target and meaningful outcome

The unchanged root is `SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Keep the same source, scope, generated problem, satisfying assignment and one
source witness. Target the original literal constructor's contribution to this
root. Use the adopted all-payload L1 rule at the original `(q,r,e₀,ξ,ω)` and
establish the actual independent Value/Effect generation and solution-readout
equation, then consume it at the literal induction edge. Keep all literal
payloads, contextual-effect obligations, checking/conversion alternatives,
source forms and every other constructor. Do not assume `LiteralAtom`, a source
judgment, a declaration/readout law, or the desired conclusion.

Success is one of:

1. A derivation-backed equation in the original carriers, independently
   reviewed as conforming to the fixed source/algorithm, followed by an
   independently reviewed theorem applied to the unchanged parent literal
   edge with the same witness; or
2. A precise `MODEL-INCOMPLETE` result identifying the first missing equation
   and authority owner, without packaging it as a conditional theorem.

A source-generation rewrite alone, R220's structural fragment alone, a theorem
whose premise is `LiteralAtom`, or a selected ground type table is not success.
The whole root remains open until all constructor edges compose. Counts remain
0/4 roots and 0/5 packages unless a reviewed parent application actually
removes a premise.

## Governing authorities and fixed semantics

- `notes/design/2026-11-02-literal-l1-adoption.md` (SHA-256
  `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`):
  eight original payload forms; `Value(literalType(payload))`; the same raw
  literal value; `Return = Comp(empty, τ)`; original root, event, scope,
  occurrence and shared witness; all checking/conversion alternatives and
  enclosing permission, inflow, residual and future obligations retained.
- R213 fixed model and its gate:
  `tasks/agent-loop/sprints/fixed-inference-model-r213.md`; if the source
  equations needed here remain open, stop proof activation with
  `MODEL-INCOMPLETE`.
- R214 audit:
  `notes/theory/2026-11-02-literal-independent-equation-r214.md`; the
  one-sided lower-bound candidate is falsified, and source sorts, Simple-sub
  graph readout and `sameScoped` are not yet identified.
- R220 structural fragment:
  `notes/theory/lean/YulangClosure/AbstractGeneratorDenotationR220.lean`;
  mutual atom bounds and an effect-bottom bound force exact graph nodes at its
  supplied coordinates, but it has no original carrier embedding, endpoint
  allocation, literal declaration, Return or shared-witness bridge.
- Original source interpretation/generation and source syntax, the pinned
  Simple-sub regular graph semantics, Contracts, and R221's source evidence.
  Reauthenticate all pins before freezing the equation.

No new language semantics are authorized by this packet. If the selected
original algorithm or existing source authority does not determine the
independent generator/readout equation, report that exact gap for Luna to
adjudicate; do not choose a different rule or narrow the source domain.

## Two lanes and activation gate

**Primary source-model lane — Luna.** Own the original-carrier equation and
`notes/theory/2026-11-02-original-literal-carrier-r231.md`. Inspect the actual
source constructor/generator and the existing satisfaction/readout carriers.
Separate intrinsic synthesis from `writtenTarget`; preserve the original root
and event. Reuse the all-payload L1 authority and R220's exact atom/bottom
rigidity only where their stated hypotheses are actually supplied. Falsify
payload loss, payload-independent value confusion, non-ground or top readout,
root/event changes, and annotation-port collapse.

**Proof lane — conditional, not yet active.** Reserve
`notes/theory/lean/YulangClosure/OriginalLiteralSolutionReadoutR231.lean` and
`tasks/agent-loop/inbox/original-literal-realization-r231-proof.md` for a
registered `lean_prover`, ≤3,000 seconds. Do not spawn/activate it until a fresh
independent source-model conformance review confirms every equation needed by
the literal theorem is derivation-backed and noncircular in the original
carriers. On activation, construct generation, every-solution readout,
descriptor/value/root/event retention, selected Value/Result and pure Return,
then apply the theorem to the original parent literal edge. If any equation is
open, no proof worker and no Lean theorem file.

**Implementation/source lane — registered researcher, read-only, ≤900 seconds.**
Own only `tasks/agent-loop/inbox/original-literal-realization-r231-source.md`.
Trace the literal producer in `crates/yu-solver/src/candidate_source.rs`, fact
admission in `crates/yu-solver/src/lib.rs`, and necessary consumer/readback in
`crates/yu-solver/src/shadow_apply.rs`. Authenticate exact occurrence,
payload, endpoints, Value/Effect terms and source coordinates. Report a complete
authorized path or `NO_SAFE_CODE_SLICE`; no Rust edits, builds, Cargo or tests.
This lane cannot establish the original mathematical equation by itself.

**Fresh model conformance review, ≤600 seconds.** Once Luna freezes the model
note and source evidence, assign a nonauthor `compiler_referee` or
`spec_auditor` to check exact L1 fidelity, source independence, original
carriers/coordinates, every-satisfying-solution quantifier, annotation and
contextual-effect boundaries, falsifiers, and whether the proof activation
gate has genuinely passed. A proof author cannot review the equation. If the
gate passes, a separate fresh review of the frozen theorem and parent
application is required.

## Exact leases, dependencies and resources

Primary writable paths: this contract, `tasks/agent-loop/current.json`, and
`notes/theory/2026-11-02-original-literal-carrier-r231.md`.

Source lane exact output: `tasks/agent-loop/inbox/original-literal-realization-r231-source.md`.

Conditional proof outputs (inactive until gate passes):
`notes/theory/lean/YulangClosure/OriginalLiteralSolutionReadoutR231.lean` and
`tasks/agent-loop/inbox/original-literal-realization-r231-proof.md`.

Review exact output:
`tasks/agent-loop/inbox/original-literal-realization-r231-review.md`.

Aggregate active-work budget ≤4,800 seconds; zero Astra. Use only the existing
`notes/theory/lean/.lake/build`; current measured size 133,953,489 bytes and
unchanged absolute ceiling 199,894,996 bytes (64 MiB above R230 baseline).
Before any Lean build, Luna must whitelist exact outputs under that directory
and stop if any other output or cap overrun is required. No tests/default build.
No path-lease override or new capacity release is part of this contract.

## Stop, review, parent and Git gates

Stop if a pin changes, the authority requires a new semantic choice, the
equation depends on source judgment/readout, a counterexample is found, or the
resource envelope is exhausted. Preserve all raw payloads and existing
alternatives. A failed candidate is recorded with its falsifier; it does not
refute L1 unless it is a source-qualified counterexample.

The source-model equation review precedes Lean proof activation. The final
theorem review must include printed type and complete axiom audit, all eight
literal forms, original port coordinates, same-witness application and exact
remaining parent premises. Rust correspondence and production remain separate
gates. At a coherent reviewed checkpoint, Luna alone stages explicit paths,
inspects the full outbound range and performs a non-forced push.

Next consultation trigger: model-gate decision, semantic counterexample,
authority/dependency/lease/resource change, integration seam or R231 closeout.
