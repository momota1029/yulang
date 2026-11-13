import Yulang.GeneralDictionaryIdentityCurrentEvidence

/-! Actual Shared source formation preserves registry metadata even across
refresh and reobservation. Point location follows from a current source slot. -/
namespace Yulang.GeneralDictionarySharedMetadata
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalIdentityLeaf
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : Tracked roles}

theorem formed_metadata (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    GeneralNominalCandidates.Metadata registry state.current.context := by
  induction formed with
  | initial context source => exact source.metadata
  | @update before after formed step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue => exact ih
      | equate => exact ih
      | reobserve => exact ih
      | refresh context certificate source member unknown known =>
        refine ⟨ih.1.trans certificate.refines.constructors.symm,?_⟩
        dsimp only [regenerate]
        rw [certificate.interpretation]
        exact ih.2
    | install packet support enabled novel guard =>
      change GeneralNominalCandidates.Metadata registry packet.context
      rw [enabled.1.2.1]
      exact ih
    | merge => exact ih

theorem locate_point (point : Point occurrence input)
    (slot : Fin context.state.base.slots) (source : context.state.base.source slot = input) :
    GeneralNominalCandidates.arguments context occurrence = some [(slot,slot)] := by
  unfold GeneralNominalCandidates.arguments
  rw [point]
  simp [GeneralCandidateBoundaryParts.locate,
    (GeneralDictionaryBinderLocations.sourceSlot_exact context.state.base input slot).mpr source]

theorem identity_current_evidence
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (shape : Shape packet.declaration) (input : Nat)
    (point : Point packet.site.occurrence input)
    (slot : Fin state.current.context.state.base.slots)
    (source : state.current.context.state.base.source slot = input)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model
      packet.site.occurrence (.node packet.declaration.id []) :=
  GeneralDictionaryIdentityCurrentEvidence.recorded_current_evidence formed packet member shape input
    point slot source (locate_point point slot source) (formed_metadata formed) model valid

end Yulang.GeneralDictionarySharedMetadata
