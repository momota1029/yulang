# R331 EI construction — frozen partial result

Assignment-ID: original-source-ei-interpretation-r331
Handoff revision: 1
Sprint/contract: R331, `tasks/agent-loop/sprints/source-environment-ei-r331.md`
Contract SHA-256: `d81ee0eace9b646dddfdfd001eac1317a3ec99d3435d2c15cdeb04f4a9727ae7`
Baseline: `839f7e3aa` (primary supplied; no Git operation)
Author/worker: `/root/r331_ei_core`; no descendants or coauthors.
Requested model/effort: `gpt-6-astra` / `medium` by assigned role; observed model/effort: UNKNOWN.
Runtime identity beyond the current canonical worker path: UNKNOWN.
Outcome: **CONDITIONAL partial construction plus interface falsifier. Parent OPEN.**

## Parent and actual application

Original assignment: EI §§3–5 / GR1–GR5, actual selected R330 source EI-All
interpretation and licensed source child for the existing relational Union,
with all original arms, live-world/response/future/whole-action quantifiers.
The original R306 `source_contribution_registered` still needs its
`child : DeclContribution graph old operators left raw childNode
(sameCatalogue ▸ packet)`. Neither that child nor R159 logical admission or
computation `Checking` was constructed here.

The achieved subedge is R311 `calleePhaseBody` / `calleeSuffix` / `tailBody`:
`ReturnInputs` now constructs `tailBody.Holds (Meaning inputs)` rather than
accepting that whole tail as an input. `callee_phase_from_original_operands`
applies this construction under **every** original CalRet-incidence binder.
`selected_source_phase` applies it to R330's actual selected request and proves
the original description-scope equation. This is principally a composition of
existing R310/R311 elimination/introduction lemmas, plus primitive-history
induction; it is not a complete new EI semantic model or an unconditional
actual-source instance. No R293 endpoint adapter, fake Decoded environment,
generated Inputs interpretation or manufactured Call OperatorContract was added.

## Exact theorem surface

Namespace: `YulangClosure.OriginalSourceEIInterpretationR331`.
Full elaborated theorem types and complete axiom output: `/tmp/yulang-r331-ei/audit-3.log`.
The source declarations also give every explicit quantifier and hypothesis.

- `primitive_input_sound`: an exact registry leaf, successful resolution and
  its original guard precondition imply the corresponding primitive guard.
- `checked_return_from_operands`: original callee membership + actual Return
  form + original value-level finite Proof imply SAME returned Function membership.
- `tail_from_original_operands`: `ReturnInputs` and sound recursive checking
  leaves imply R311's complete existing `tailBody` clause.
- `all_live_receiver_developments`: the same inputs imply the original receiver
  clause for **every** compatible current event, checked challenge and execution.
- `argument_designated_force`: independently checked whole carrier and an actual
  demand/Force imply compatibility, original incidence and full trace clause.
- `same_return_live_function`: every compatible later event preserves the same
  original returned value's Function membership and actual provider.
- `steps_from_original_primitives`: ordered primitive leaves imply `stepsBody`,
  retaining all earlier raw observations in every later primitive signature.
- `callee_phase_from_original_operands`: genuine old callee prefix membership,
  a prefix guard derivation, and separately typed operands at every original
  CalRet incidence construct the existing R311 `.callee` phase.
- `selected_source_phase`: the preceding theorem at `R330.request origin`,
  paired with its computed original description-scope equation.
- `selected_prefix_requires_original_declaration`: even this partial selected
  callee phase requires an actual successful prefix primitive resolution.
- `unchecked_reference_preserves_leaf`: changing `PrimitiveGoal.reference` and
  `.use` retains the same `PrimitiveLeaf` identifier/entry. The constructed
  `change_unchecked_reference` exposes the exact limitation: PrimitiveLeaf
  authenticates only `goal.signature`. This does **not** say a resolver that
  independently checks the Key is unsound; that resolver is the missing input.

`ReturnInputs` contains only original callee trace membership, original Return
form, same-value finite Function checking, Function sort, actual provider,
CalRet guard derivation and independently checked whole arguments for each
original reify-incidence carrier. It contains no EI body, EI membership,
source child, desired readback, target computation Checking or arm omission.
PrimitiveInput alone does not authenticate a source Key; the result remains
conditional until the actual resolver's source correspondence is established.

## Source evidence, reused work and exact residual

Authority read: computed-call-result-constructor §§2–5; generated-computed-result-
correspondence GR1–GR5; computed-call-bind-result §§2–5; current inference rules.
R330 supplies actual source `[13]` / ViewLogic `[12]` ownership; R310 supplies
scoped operand syntax; R311 supplies original positive clauses and old Function/
carrier eliminations; R328 old meanings are untouched. R312/R313 actual CalRet
and argument bridges were inspected, but still require original membership and
primitive leaves. R321 supplies the concrete tick declaration for a separate
formal literal-response consumer, explicitly not its original EI response bridge.
No fresh native execution/probe or compiler correspondence theorem was produced.

First missing source input: authenticated interpretation of
`primitiveGoal (R330.request origin) declarations .calleePrefix ...`, linking
its full typed Key, use, original source position and signature to an actual
original primitive declaration with its genuine precondition. A focused search
of the original Lean sources found uses of R311's resolver interface, but no
concrete selected-source resolver/PrimitiveDeclarations instance providing it.
The retagging theorem shows why a signature-only PrimitiveLeaf cannot supply
this source correspondence by itself.

Further irreducible data before full EI registration: (1) full original typed
Request response/current-world telescope and resume readout at the selected
source owner; `OriginalSourceEnvironment.ResponseData` is an opaque observation
plus receipt and `LocalAdmissions.response` is a separate predicate, not that
interpreter; (2) original lawful whole-tuple action/incidence maps tying receiver
Return/provider/future to the same prior receiver trace; (3) every original arm's
own environment/local telescope and independent source law. R311 itself labels
those missing cases. Its incomplete `phaseBody` was deliberately not installed
as R328 `Generated`, and no arbitrary `Generated` argument is presented as EI.

Mutual TODO `R331-EI-SOURCE-PRIMITIVES-1` (Luna/source-law owner): supply or
construct the selected Key-authenticated primitive interpretation and typed
response/current-world action from original declarations. Falsifier: alter
source Key/use while retaining signature; the resolver must reject or provide
a genuine source equivalence, and preserve every admitted response/live event.
Then construct full EI result/arm clauses and the licensed Call child before
using R306/R293. This is a proof/source-model TODO, not production edit authority.

## Checks and resources

Pinned Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Observed versions: Lake 5.0.0-src+eb6cafb; Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

1. Bundled `check_lean.py --project /tmp/yulang-r331-ei/project ... --timeout 400`
   failed (exit 1) rebuilding unchanged R315 at `-M1024`; retained `check-1.log`.
2. Copied independently built dependency artifacts from the environment lane's
   isolated project; R315's local `-M2048` requirement is recorded by that lane.
   No source/toolchain/manifest change was made to overcome the memory failure.
3. Direct `lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure/OriginalSourceEIInterpretationR331.olean
   YulangClosure/OriginalSourceEIInterpretationR331.lean`: final exit 0, no warnings,
   `/tmp/yulang-r331-ei/direct-3.log`.
4. Direct `lake env lean -j1 -M1024 /tmp/yulang-r331-ei/Audit.lean`: exit 0;
   all 11 theorem types and axiom lists printed, plus all input structures.
   Earlier syntax/include repairs and one stale-artifact audit are retained in
   prior logs and are superseded ONLY by the successful `direct-3`/`audit-3` pair.

Axioms: `primitive_input_sound`, `steps_from_original_primitives`, and
`unchecked_reference_preserves_leaf`: none. The six non-selected semantic
construction theorems: `[propext, Quot.sound]`. `selected_source_phase` and
`selected_prefix_requires_original_declaration`: `[propext, Classical.choice, Quot.sound]`.
No sorry/admit/project axiom/bypass in the authored source; no nonstandard
axiom in the complete theorem dependency audit. A clean full Lake build is NOT
claimed. Heavy slot released to Luna after final direct checks.

Finite scope: five substantive stages (source/authority audit, operand/tail
construction, selected consumer application, primitive-interface falsifier,
checker/repair/audit); no descendants. Active duration not instrumented exactly;
conservatively charge 1800 seconds, no budget renewal requested or implied.

## Frozen artifacts and writer stop

- `notes/theory/lean/YulangClosure/OriginalSourceEIInterpretationR331.lean` SHA-256 `2aec3d3381ce8e99925c164be2d14a1a0f12e9ac1f05dc34cacb3d49a9195a9d`
- Direct dependency R330 SHA-256 `fd8ea7bed1bc42f5ed6ff32dbf01b812d8967e6cc33a4536ced74bb5710c375e`
- Direct dependency R311 SHA-256 `7d230579d98b9034e62192330f98b2578629635e9810e7a7ff9195a29c813de6`
- Full 55-file source/import inventory `/tmp/yulang-r331-ei/dependencies.json`
  SHA-256 `ba82b7017f170e29e8318b65e0b123b9d4f78e7845cc442b387fc43f4db43f40`
- Full audit `/tmp/yulang-r331-ei/audit-3.log` SHA-256 `b35a396f5619100fcd6899b4c15b2fef96f725a48c64896e45749c9059135c61`

All new/scratch paths: this one inbox, the leased Lean module, and the exclusive
`/tmp/yulang-r331-ei` tree (isolated source/cache copy, dependency inventory,
Audit.lean and all retained check/repair logs). No writes elsewhere; no Git.
Worker state: STOPPED WRITING after this handoff freeze; no background checker
or descendant. Candidate is ready for independent review as a **partial,
conditional research result**, not as fulfillment of the full R331 EI lane or
as an approved production/theorem closure. Next work needs actual source-law
inputs/owner assignment, not another renamed tail lemma.
