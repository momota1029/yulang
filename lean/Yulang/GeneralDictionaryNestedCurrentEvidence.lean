import Yulang.GeneralDictionaryNestedBranchTransport
import Yulang.GeneralDictionaryRecordedInspectionFacts
import Yulang.GeneralDictionaryRefinedLocations

/-! Current Instance/Evidence for a real recorded finite nominal-variable packet.
Old completion, current lookup, binding equality, projection and request coverage
are derived from actual history and source-preserving refinement. No Stable or
current branch-model hypothesis is hidden here. Arbitrary reobservation and
structural/scalar query trees remain outside this theorem's syntax scope. -/
namespace Yulang.GeneralDictionaryNestedCurrentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalInspection
open GeneralDictionaryNestedRefinement GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

theorem current_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (interpretation : state.current.context.interpretation = packet.context.interpretation)
    (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence packet.declaration.id
      (GeneralNominalAllocation.children state.current.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked (bindings state.current.context.state
          (report state.current.context packet.declaration (packet.bounds.map (mapBounds refinement.base.embed))))) := by
  have done := GeneralDictionaryRecordedInspectionFacts.finished packet root state reachable recorded
  have captures := GeneralDictionaryNestedRefinementReplay.bindings_preserved packet.context state.current.context
    refinement interpretation packet.declaration packet.bounds scope done
  refine ⟨packet.declaration,GeneralDictionaryVariableClauseCatalog.recorded_visible packet root state reachable recorded,
    packet.checked,rfl,GeneralDictionaryRecordedInspectionFacts.role packet root state reachable recorded,
    packet.bounds.map (mapBounds refinement.base.embed),?_,?_,?_,rfl,?_,?_⟩
  · exact GeneralDictionaryRefinedLocations.arguments packet.context state.current.context refinement
      packet.site.occurrence packet.bounds (GeneralDictionaryRecordedInspectionFacts.located packet root state reachable recorded)
  · rw [GeneralDictionaryNestedRefinementReplay.report_refined packet.context state.current.context refinement
      interpretation packet.declaration packet.bounds scope done]
    exact (finished_map _ _).mpr done
  · exact ⟨GeneralDictionaryRecordedInspectionFacts.root_defined packet root state reachable recorded,
      GeneralDictionaryRecordedScalarIntervalEvidence.generated_known packet root state reachable recorded _ captures⟩
  · exact GeneralDictionaryRefinedLocations.metadata packet.context state.current.context refinement interpretation
      packet.registry (GeneralDictionaryRecordedInspectionFacts.metadata packet root state reachable recorded)
  · exact GeneralDictionaryNestedBranchTransport.recorded_branch root state packet reachable recorded refinement
      interpretation scope done model valid

theorem selected_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (interpretation : state.current.context.interpretation = packet.context.interpretation)
    (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence key children := by
  have current := current_instance packet root state reachable recorded refinement interpretation scope model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected packet.registry state.current
    packet.site.occurrence model packet.declaration.id key _ children current
    (GeneralNominalValueBoundary.selected_old selected)
  simpa only [same.1,same.2] using current

theorem selected_evidence (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (refinement : GeneralNominalRefinements.Refines packet.context.state state.current.context.state)
    (interpretation : state.current.context.interpretation = packet.context.interpretation)
    (scope : NominalOnlyMany (queries packet.context.state packet.context.interpretation packet.declaration))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence packet.registry state.current.context model) children dictionaries) :
    Evidence packet.registry state.current.context model packet.site.occurrence (.node key dictionaries) :=
  evidence_node packet.registry state.current.context model packet.site.occurrence key children dictionaries
    (selected_instance packet root state reachable recorded refinement interpretation scope key children selected model valid) given
end Yulang.GeneralDictionaryNestedCurrentEvidence
