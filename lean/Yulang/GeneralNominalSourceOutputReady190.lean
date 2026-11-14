import Yulang.GeneralNominalOutputCoverage189
import Yulang.GeneralNominalSourceVariableInstall189

/-! Requested-output coverage discharges actual effect readiness at an initial
source, independently of the number or shape of the declaration's heads. -/
namespace Yulang.GeneralNominalSourceOutputReady190
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem source_effects_ready
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles)
    (coverage : ∀ output ∈ root.demand.outputs,
      ∃ equation ∈ candidate.packet.declaration.associated, equation.name = output.name)
    (translated : ∀ equation ∈ candidate.packet.declaration.associated,
      GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate
        candidate.packet.context.state.constructors candidate.packet.context.interpretation (normalize equation.rhs))) :
    EffectsReady state.core root candidate := by
  apply GeneralNominalOutputCoverage189.effects_ready state.core root candidate _ translated
  intro output member
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,covered⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  exact coverage output (requestEq ▸ member)

end Yulang.GeneralNominalSourceOutputReady190
