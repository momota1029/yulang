import Yulang.GeneralNominalSourceVariableInstall189
import Yulang.GeneralNominalInitialNamedEvidence189

/-! Stable initial single-variable leaf selection with named output requests
produces the actual model-indexed source Evidence. The same arbitrary current
model is retained. General reachable states and nonleaf heads remain outside scope. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSourceVariableEvidence189
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem stable_selected_evidence (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (stable : (boundary roles).Stable registry state root)
    (selected : Local registry state root (.selected key children))
    (declarations : ∀ declaration ∈ registry.declarations, declaration.id = key →
      (∃ name, declaration.head = [.var name]) ∧ declaration.requirements = [] ∧
      (∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name) ∧
      ∀ equation ∈ declaration.associated, GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate state.core.erased.current.context.state.constructors
          state.core.erased.current.context.interpretation (normalize equation.rhs))) :
    children = [] ∧ ∀ model, Models state model →
      (boundary roles).Evidence registry state model root (.node key []) := by
  obtain ⟨candidate,support,frame,kids,enabled⟩ :=
    GeneralNominalSourceVariableInstall189.selected_source_candidate checked source selected declarations
  have leaf := (declarations candidate.packet.declaration frame.visible frame.key_eq).2.1
  have committed := GeneralNominalInitialLeafEvidence189.stable_committed stable candidate frame enabled
  refine ⟨kids.symm.trans (GeneralNominalHeadLeafPlan189.children_empty candidate leaf),?_⟩
  intro model valid
  have ready : EffectsReady state.core root candidate := by
    simpa only [frame.occurrence_eq] using enabled.ready
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key [] [] (GeneralNominalInitialNamedEvidence189.committed_instance source candidate frame leaf ready committed model valid) .nil

end Yulang.GeneralNominalSourceVariableEvidence189
