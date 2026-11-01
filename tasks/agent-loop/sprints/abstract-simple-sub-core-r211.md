# Sprint R211 — endogenous abstract Simple-sub core

Status: **ACTIVE**. Primary admits this bounded mathematical core sprint under
the resumed Yulang source-inference goal.
Branch / baseline: `yulang3` / `607e2ce81`; no new environment or cache.
Parent roots: unchanged `Contracts.SourceProblem.InferenceSoundness`,
`PrincipalCoverage`, `InferenceTermination`, and `SourceScopedCoverage`.
R210 remains `CLOSED_INCOMPLETE`; its outcome is not reopened.

## Fixed outcome and success evidence

Construct one concrete, source-independent Simple-sub core problem/state and
endogenous transition relation from the approved structural/effect term
algebra and selected constraint, extrusion, intrusion, and generalization
operations. Prove a whole-run soundness theorem:

```text
CoreRun (CoreProblem.initial p) final → CoreAccepted p final →
  CoreReadout p final satisfies p.originalConstraints
```

`initial`, `step`, acceptance, and readout must be definitions of this model.
The core must own pending work, bounds, graph allocation, levels, actual
parent/copy events, equality state, and publication/use state. Derive every
history, decoder, occurrence, and qualification consumed by reusable lemmas
from that run. Do not accept an externally supplied successful history or
preservation certificate as the model.

Retain Value and Effect kinds; bottom/top, union/intersection; all four
Function ports; records, tuples, variants; level-aware extrusion; actual
polarity-bearing parent/copy occurrence identity; the selected Value-reference
SCC qualification and equality operation; and generalization/publication
boundaries. The model is for arbitrary finite abstract constraint inputs; it
does not narrow or replace the original source domain.

Success is the frozen concrete definitions plus the checked theorem above and
its exact printed type and complete axiom audit, independently reviewed for
source authority, non-vacuity, and coverage of every listed operation. A
theorem conditional on supplied histories, `LawfulStore`, terminal
certificates, arbitrary step choices, or externally supplied graph/reference
data does not meet the gate unless those objects are constructed by `initial`
and `step` from `CoreProblem`.

**Root accounting:** this core theorem alone changes neither original root nor
the existing 0/5 dependency-package count. Report `0/4 roots; 0/5 packages`
unless a reviewed application to an unchanged parent premise is exhibited.
`InferenceSoundness` still needs independent source generation/solving and the
same-scoped source readout. Literal L1 is adopted; its generation/readout
bridge remains open. Principality/order and the full original source
termination bridge remain separate.

## Authority and frozen dependencies

The research order follows the user's root-first plan and the 2026-10-11
top-level inference principles. Use the selected parent/copy SCC decision and
the Simple-sub accumulation/SCC sources below. `SimpleSubGrowingInference`
and its lattice counterpart are reusable implementations of local structure,
not authorities to assume a complete algorithm. The unreviewed rebuilt-core
note is a locator only. Return to Luna if two governing authorities conflict;
do not invent semantics to fill a gap.

SHA-256 pins:

```text
Contracts.lean                                      2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
SimpleSubConstraintSyntax.lean                     a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6
SimpleSubConstraintSoundness.lean                  33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293
SimpleSubLatticeInference.lean                     c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3
SimpleSubLatticeGrowingInference.lean              1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0
SimpleSubGrowingInference.lean                     865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce
SimpleSubRegularCompletion.lean                    d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa
SimpleSubRegularDecision.lean                      6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d
SimpleSubLatticeDecision.lean                      a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9
SimpleSubScopedPublication.lean                   d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f
SimpleSubGeneralizationSoundness.lean               3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246
top-level inference principles                     7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
parent-copy SCC decision                           6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b
complete bound accumulation                        f4d3bd7e89ae26ecba0baeaaa351e82037ff0cf268c815e64b638dbbabfb2493
Value-reference SCC                                8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6
```

## Owner, stages, and exact leases

Primary/Luna fixes the model contract and adjudicates semantic choices. One
registered `lean_prover` owns the only new Lean module and its one handoff:

- `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean`
- `tasks/agent-loop/inbox/abstract-simple-sub-core-r211-proof.md`

Stage A (1,200 active seconds): define and freeze `CoreProblem`, `CoreState`,
computed `initial`, endogenous `step`, accepted/readout relations, and the
actual finite run relation. List exact constructors and show how each
selection follows the pinned authority. If this cannot be done without
inventing a transition or taking a decisive source/graph law as an input,
freeze the first exact missing equation and stop; do not substitute a
conditional local theorem.

Stage B (1,800 active seconds): prove whole-run soundness against the original
constraints for the frozen definitions. No termination claim is required in
this sprint. Use at most two focused `check_lean.py` invocations in the
existing pinned Lean 4.35.0 project, 120 seconds each, one CPU, 1 GiB RSS. Do
not create a cache, environment, target, scratch tree, or Rust build.

Fresh independent review (600 active seconds) is Luna-assigned after the
module and handoff freeze. The reviewer checks authority, exact definitions,
non-vacuity, all listed operations, theorem type, and axiom audit. A model
author cannot review their own artifact.

The registered prover reports actual session/runtime receipt, model/effort
when available, exact checks, every declaration/type/axiom audit, source
hashes, and writer cessation. Only Luna may integrate, update state, stage,
commit, or push. No Rust lane is opened by this packet.

## Falsifiers and stop conditions

- A legal endogenous accepted run whose readout fails an original input
  constraint (including a counterexample arising after extrusion or
  intrusion) falsifies the theorem.
- A model whose accepted relation can be made true vacuously, whose solver
  steps or semantic certificates are supplied from outside the run, or whose
  union/intersection, effects, Function ports, qualifying intrusion, or
  generalization operation is missing fails conformance review.
- Stop at the first unresolved algorithm authority, non-finite allocation
  rule, unconstructed Value-reference/SCC input, input-hash change, output
  collision, missing cached dependency, or resource boundary. Do not narrow
  source forms or alter the pending typed-Union question.

## Next use and exclusions

After review, use the concrete core definitions to plan a separate
accessibility proof against the same `initial`/`step`; then build the complete
original-source generation/readout bridge and apply results to the unchanged
roots. Do not report this core theorem as Yulang source inference soundness,
principality, termination, Rust correctness, or production readiness.
