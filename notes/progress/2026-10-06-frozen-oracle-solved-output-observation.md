# Frozen Oracle: solved call-site output observation

Date: 2026-10-06
Status: bounded historical characterization; primary-authored, independent review pending
Yulang3 baseline: `e300a6a1a1241e18793889c4bdb9aab2cd07ff79`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Claim class: downstream typed-observation mechanism; no semantic or implementation authority

## Question and result

The current open source producer must associate an original call/output
occurrence with its complete invocation output, typed path, owner/receiver and
receipt while preserving the original source identity and joint relation
before the comparison whose result is later consumed. Existing Frozen Oracle
archaeology found source-side application boundaries and, separately,
runtime provider attachment. This bounded trace asks whether the old system
also retained a typed call-site output observation that joins source expression
identity to solved type endpoints and solver evidence.

It did: after task solving, the specializer emits one `RuntimeEvidenceSite` for
each retained expression whose constructor is one of the selected forms. An
ordinary `App` whose callee is not a direct effect-operation `Var` is retained
as `App { callee, arg, argument_contract }`. If the solved expression has a
consumer and is function-like or carries an argument-effect contract, its
boundary stores actual and consumer types plus their slot IDs. A runtime
evidence node then joins the site and its child expressions to the relevant
slot evidence in the solved graph.

This is the closest historical typed output-observation mechanism found in
this pass. It is deliberately downstream of solving: it observes solved
actual/consumer endpoints and graph slots. It does not derive the current
source producer, create `beta`/`Slots(beta)`, establish a pre-comparison
admission relation, or construct the required typed receipt/receiver map. For
an opaque local formal call such as `f x`, the provider-requirement collector
previously traced does not recognize the call as a direct `EffectOp`; the
post-solve site record does not repair that missing source-side correspondence.

## Historical path

All source paths below are relative to the frozen Oracle tree.

1. `specialize2/emit.rs:45–60` solves each runtime root with
   `TaskSolver::solve_root_expr`, then calls
   `runtime_evidence.push_solved_task` with the original root expression ID and
   the `SolvedTask`. Instance bodies use the same sequence at `:166–183`.
2. `specialize2/task_solver/finish.rs:121–153` solves role demands and slots,
   then iterates expression-type entries in expression-ID order. For each
   retained expression it resolves the actual and optional consumer types and
   stores `SolvedExprType { actual, consumer, actual_slots, consumer_slots }`.
   Slot references are collected from the type endpoints before resolution.
3. `specialize2/runtime_evidence.rs:1952–1984` turns those solved entries into
   sorted `RuntimeEvidenceSite`s and `RuntimeEvidenceExprType`s. In
   `RuntimeEvidenceSite::from_expr` (`:1709–1745`), a direct operation call is
   distinguished from ordinary application by checking whether the callee is
   a `Var` resolving to an effect operation. Every other `App` is retained with
   its source callee/argument expression IDs and a Boolean annotation-contract
   lookup result.
4. `RuntimeEvidenceBoundaryCandidate::from_expr_type` (`:1822–1835`) requires
   a solved consumer and retains the actual/consumer types and slot vectors
   when either endpoint is function-like or an argument-effect contract is
   present. This is an observation of an already solved boundary, not an
   independently interpreted source constraint.
5. `RuntimeEvidenceNode::from_site` and `slots_for_site` (`:1567–1601,
   :2383–2404`) union the site's own type slots, boundary slots and child
   expression slots, then attach references to weighted bounds, edges and
   effect-subtraction evidence in the solved graph. The join key is the
   expression/slot identity retained by this specialization task.

The source-side identity is useful: an ordinary application does not vanish
from this evidence surface merely because it is not a recognized direct
operation call. But the record's provenance starts from `ExprId` plus solved
type slots; the inspected path does not recover an original source occurrence
tree, source owner, receiver activation, or receipt certificate. The full
source-to-expression lowering and other evidence producers were not traced.

## Correspondence limits

| Historical mechanism | Resembles | Does not establish |
|---|---|---|
| `RuntimeEvidenceSite::App` retains callee/argument expression IDs | Ordinary Apply source occurrence retention | Complete original `beta`, `Slots(beta)`, or static use inventory |
| Solved actual/consumer endpoint and slot vectors | Typed output address and solved boundary observation | Q-independent source formation or original joint `(nu,K,D)` |
| Node-to-slot evidence references | Typed graph evidence attached to a call-site record | Typed receipt, owner/receiver relation, or source capture/rebind/read correspondence |
| Direct-effect-call classification | One historical producer for known operation sites | Provider/effect incidence for opaque calls through an unknown formal |

These mechanisms may be useful as historical design clues for separating
source occurrence identity from solved output observation. Their order matters:
the site-to-endpoint record is constructed from a `SolvedTask`, after role and
slot solving. Reusing it as the current source producer would make the
producer depend on the comparison/solution it is meant to precede. The old
artifact therefore supplies an analogy for a later observation join, while
leaving the current pre-query source rule open.

No Oracle output, test expectation, or runtime behavior is treated as
authority. This report makes no compatibility claim and proposes no current
semantic rule. It neither weakens nor closes soundness, principality, source
adequacy, production-cutover, or differential-shadow gates.

## Scope and checks

This was a bounded static read of the pinned `emit.rs`, `task_solver/finish.rs`,
and `runtime_evidence.rs` paths, plus call-site and type-definition searches in
the frozen `specialize` subtree. No Oracle build, execution, tests, compiler
edits, randomized probe, or Git mutation occurred. No whole-repository absence
claim is made. Independent review remains pending; this checkpoint is
research-only.
