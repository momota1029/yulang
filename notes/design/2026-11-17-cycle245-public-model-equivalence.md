# Cycle245: public model equivalence for actual table rebase

The earlier checkpoint had only a one-way model map. This cycle now closes the
reverse direction under explicit representation conditions, first for an
antisymmetric model and then, importantly, without antisymmetry for the actual
CommonNominalFullCarrier.model using proved constructor congruence laws.

`GeneralPresenceAbsorb245`: when old definitions are External and Coherent and
fresh targets stay within old targets, old substitution absorbs fresh
substitution. Rows stay unchanged; the law holds for arbitrary actual TyTerm,
Atom and lists of atoms. No semantic assumption is needed for this syntax law.

`GeneralPresenceModelCongruence245`: a subtype preorder whose primitive
constructors respect mutual subtyping preserves term/atom/list interpretation
under pointwise equivalent type assignments and equal row assignments. Every
primitive, including arrow and whole-record default, is represented explicitly.

`GeneralPresenceCommonLaws245`: those primitive laws are proved for the concrete
nominal Common carrier using its existing all-depth/all-negative-rank demand
semantics. There is no antisymmetry assumption on its syntax. In particular,
arrow input variance is reversed and default's depth-zero approximation is
handled separately. A focused50-module dependency closure was rebuilt; no
whole journal build was attempted.

`GeneralPresencePreorderExtension245`: assuming selected owner present, private
targets disjoint from other owners, old and fresh blocks External/Coherent,
fresh targets within old targets, public names outside old targets, proves for
every fixed public value-and-row assignment:

    old has a model with this exact public assignment
      iff
    actual rebased table has a model with this exact public assignment.

The new model is constructed by fresh readback; the old model by old readback.
Private type values may be only equivalent, while every public Comp value is
literally preserved. No retained-block External premise is needed for a single
step's semantic equivalence. Such a premise can still matter to later steps.

`GeneralPresenceRebasePlan245`: actual `rebase` calls are executed along a finite
list. A SafePlan certifies each intermediate state's conditions separately.
Their public equivalences compose, with a concrete Common-model specialization.
`GeneralPresenceRebaseExample245` verifies a two-owner, two-edit example with
rewritten base constraints and genuinely changed private definitions.

## Still not claimed

- SafePlan production by actual source/install/promotion/Refresh operations.
- That arbitrary fresh definitions encode the intended aggregate obligations.
- A finite bound on generated plan length, solver transition accessibility,
  scheduler simulation, or EvidenceNode completion.
- Preservation of an unrewritten query that reads a private target.
- Full SourceBoundary current/history/cache metadata integration.
- The antisymmetric-model theorem applies to Common syntax; the preorder law
  theorem is the one used for Common.

The auxiliary three-owner check-closure counterexample and missing-reflexivity
countermodel do not refute a language claim and are not asserted reachable from
source programs. They delimit insufficient proof interfaces.
