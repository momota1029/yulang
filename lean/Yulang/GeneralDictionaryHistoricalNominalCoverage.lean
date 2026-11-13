import Yulang.GeneralDictionaryNestedCurrentEvidence
import Yulang.GeneralDictionaryScalarRegistryIntervals

/-! Finite historical coverage for a selected current nominal node.
The witness contains syntax and actual journal provenance, not Instance,
Evidence, BranchModels or any all-model validity assertion. -/
namespace Yulang.GeneralDictionaryHistoricalNominalCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalInspection
open GeneralDictionaryNestedRefinement GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

def Supported (state : Tracked roles) (focus : Occurrence roles) : Prop :=
  ∃ packet ∈ state.current.packets, packet.site.occurrence = focus ∧
    ∃ _refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state,
      NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration)

theorem selected_instance (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (supported : Supported state focus) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  obtain ⟨packet,recorded,same,refinement,scope⟩ := supported
  have registrySame := GeneralDictionarySupportJournal.packet_registry registry root state
    (GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
      (GeneralNominalValueBoundary.reachable_formed registry state root reachable))) packet recorded
  have interpretation := (GeneralDictionaryScalarRegistryIntervals.reachable_coherent reachable packet recorded).symm
  subst focus
  subst registry
  exact GeneralDictionaryNestedCurrentEvidence.selected_instance packet root state reachable recorded
    refinement interpretation scope key children selected model valid

theorem supported_of_recorded (packet : Packet roles) (state : Tracked roles)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration)) :
    Supported state packet.site.occurrence := ⟨packet,recorded,rfl,refinement,scope⟩
end Yulang.GeneralDictionaryHistoricalNominalCoverage
