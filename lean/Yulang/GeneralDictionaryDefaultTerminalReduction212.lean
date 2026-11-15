import Yulang.GeneralDictionaryDefaultTerminalOutput212
import Yulang.GeneralDictionaryEmittedChildCount

/-! Exact terminal reduction, used only after the exhaustive EvidenceNode
provenance split. Terminal does not mean scalar or point-valued. -/
namespace Yulang.GeneralDictionaryDefaultTerminalReduction212
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepPackets
open GeneralNominalCenteredHeadCandidates (HeadModels)
open GeneralNominalCenteredHeadOutputs (HeadEquations)
variable {roles : Roles.RoleDecls} {plan : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem terminal_of_children (empty : plan.packet.children = []) :
     plan.packet.declaration.requirements = [] :=
  (GeneralDictionaryEmittedChildCount.children_empty_iff ..).mp empty

 theorem packet_iff (terminal : plan.packet.declaration.requirements = []) :
     Holds plan model ↔
       HeadModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
         plan.packet.declaration plan.packet.bounds model ∧ HeadEquations plan model ∧ Outputs plan model := by
  constructor
  · intro held
    exact ⟨(models_iff.mpr held).1,head_equations held,held.2.2⟩
  · rintro ⟨head,⟨input,fits,heads⟩,outputs⟩
    apply models_iff.mp
    refine ⟨head,input,?_,heads,outputs,?_⟩
    · intro name needed
      rcases needed with named | ⟨clause,member,_⟩
      · exact fits name named
      · rw [terminal] at member
        cases member
    · intro clause member
      rw [terminal] at member
      cases member

 theorem common_iff (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
     (terminal : effect.plan.packet.declaration.requirements = []) :
     (∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
       Holds effect.plan model ∧ effect.Holds model) ↔
     ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
       HeadModels effect.plan.packet.registry effect.plan.packet.context effect.plan.packet.site.occurrence
         effect.plan.packet.declaration effect.plan.packet.bounds model ∧ effect.Holds model := by
  constructor
  · rintro ⟨model,valid,packet,effects⟩
    exact ⟨model,valid,((packet_iff terminal).mp packet).1,effects⟩
  · rintro ⟨model,valid,head,effects⟩
    exact ⟨model,valid,(packet_iff terminal).mpr
      ⟨head,effects.1,GeneralDictionaryDefaultTerminalOutput212.outputs_of_effect effect terminal effects⟩,effects⟩

 theorem installable_iff
     (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
     (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
     (selected : GeneralDictionaryDefaultBoundary208.Local value state effect.plan.packet.site.occurrence
       (.selected effect.plan.packet.declaration.id children))
     (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
     (snapshot : effect.snapshot = state.core)
     (terminal : effect.plan.packet.declaration.requirements = []) :
     GeneralDictionaryDefaultKernel208.Installable (GeneralNominalCenteredHeadAllocEncoding.registry value) state effect ↔
       GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
       ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
         HeadModels effect.plan.packet.registry effect.plan.packet.context effect.plan.packet.site.occurrence
           effect.plan.packet.declaration effect.plan.packet.bounds model ∧ effect.Holds model := by
  rw [GeneralDictionaryDefaultAvailability208.selected_installable_iff checked reachable selected registryEq snapshot]
  exact and_congr Iff.rfl (common_iff effect terminal)

end Yulang.GeneralDictionaryDefaultTerminalReduction212

namespace Yulang.GeneralDictionaryDefaultTerminalReduction212
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepJournal
variable {roles : Roles.RoleDecls} {effect : Effect roles}

/-- Direct terminal-node assembly in every current journal model. The sole
existential witness in `common` is joint; separate witnesses are not accepted. -/
 theorem stable_terminal_node
     (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
     (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
     (selected : GeneralDictionaryDefaultBoundary208.Local value state effect.plan.packet.site.occurrence
       (.selected effect.plan.packet.declaration.id children))
     (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
     (snapshot : effect.snapshot = state.core)
     (terminal : effect.plan.packet.declaration.requirements = [])
     (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
     (common : ∃ model, Models state model ∧
       GeneralNominalCenteredHeadCandidates.HeadModels effect.plan.packet.registry effect.plan.packet.context
         effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds model ∧ effect.Holds model)
     (stable : GeneralDictionaryDefaultBoundary208.Stable value state effect.plan.packet.site.occurrence)
     (valid : Models state model) :
     GeneralDictionaryTotalEvidence206.Evidence (GeneralNominalCenteredHeadAllocEncoding.registry value)
       state.core model effect.plan.packet.site.occurrence (.node effect.plan.packet.declaration.id []) := by
  have enabled := (installable_iff checked reachable selected registryEq snapshot terminal).mpr ⟨choice,common⟩
  have empty : effect.plan.packet.children = [] :=
    (GeneralDictionaryEmittedChildCount.children_empty_iff ..).mpr terminal
  exact GeneralDictionaryDefaultCommitment208.enabled_stable_node enabled stable valid
    (empty.symm ▸ CommonRoleOutermostResolver.All₂.nil)

end Yulang.GeneralDictionaryDefaultTerminalReduction212

namespace Yulang.GeneralDictionaryDefaultTerminalReduction212
open GeneralDeclarations GeneralNominalCenters
variable {roles : Roles.RoleDecls} {plan : Plan roles}

 theorem no_output_binders (terminal : plan.packet.declaration.requirements = []) :
     plan.packet.declaration.outputBinders = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder member
  obtain ⟨clause,present,_⟩ := plan.packet.checked.produced binder member
  rw [terminal] at present
  cases present

 theorem no_output_names (terminal : plan.packet.declaration.requirements = []) :
     plan.packet.declaration.outputNames = [] := by
  unfold Declaration.outputNames
  rw [no_output_binders terminal]
  rfl

/-- Terminal associated expressions use only the implementation's input
binders; the Produced condition rules out hidden child-produced outputs. -/
 theorem associated_inputs_only (terminal : plan.packet.declaration.requirements = [])
     (member : equation ∈ plan.packet.declaration.associated)
     (used : name ∈ (GeneralDeclarationPatterns.normalize equation.rhs).variables) :
     name ∈ plan.packet.declaration.inputNames := by
  rcases plan.packet.checked.scope.2.1 equation member name used with input | output
  · exact input
  · rw [no_output_names terminal] at output
    cases output

end Yulang.GeneralDictionaryDefaultTerminalReduction212
