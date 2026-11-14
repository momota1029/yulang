import Yulang.GeneralNominalLinearNamedPlan189
import Yulang.GeneralNominalInitialNamedEvidence189

/-! Actual initial stable evidence for finite distinct-name variable leaf heads,
with named output requests allowed. This is not the unrestricted WF boundary. -/
namespace Yulang.GeneralNominalLinearNamedEvidence189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem stable_selected_evidence (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (stable : (boundary roles).Stable registry state root)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (unique : (entries.map Prod.fst).Nodup)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root (.node key []) := by
  obtain ⟨support,enabled⟩ := GeneralNominalLinearNamedPlan189.selected_named_installable
    checked source selected candidate frame entries unique query bounds names leaf ready
  have committed := GeneralNominalInitialLeafEvidence189.stable_committed stable candidate frame enabled
  intro model valid
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key [] [] (GeneralNominalInitialNamedEvidence189.committed_instance source candidate frame leaf ready committed model valid) .nil

end Yulang.GeneralNominalLinearNamedEvidence189
