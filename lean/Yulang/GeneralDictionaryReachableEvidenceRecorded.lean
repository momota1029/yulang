import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! A recorded, exact-occurrence alias class supplies selected Joint without a
semantic Joint premise. Registry size is unrestricted and the journal need not
be initial. The path is explicitly the restricted FinishedTrace: this result
must not be used for arbitrary view/carrier-changing feedback refreshes. -/
namespace Yulang.GeneralDictionaryReachableEvidenceRecorded
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralDictionaryRecursiveEvidence
open GeneralNominalJointCandidates (Joint BranchAt Related)

/-- Actual selection supplies the readiness and freshness guards missing from
an independently checked semantic instance at the same occurrence. -/
theorem selected_branch (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (model : GeneralNominalCommonBridge.Assignment)
    (key selectedKey : Nat) (children selectedChildren : List (Occurrence roles))
    (instanceRule : Instance registry state.context model focus key children)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected selectedKey selectedChildren)) :
    BranchAt registry state focus selectedKey model := by
  have identity := (GeneralDictionarySelectedInstanceCoherence.instance_selected
    registry state focus model key selectedKey children selectedChildren instanceRule selected).1
  cases selected with
  | selected safe unique =>
    obtain ⟨_,chosen,_,chosenChecked,_,_,chosenBounds,_,chosenPrepared,_⟩ := unique.1
    obtain ⟨declaration,visible,checked,keySame,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := instanceRule
    exact ⟨declaration,visible,checked,keySame.trans identity,role,
      ⟨metadata,chosenPrepared.2.1,chosenPrepared.2.2.1,bounds,located,finished,ready,model,branch⟩,
      bounds,located,branch⟩

/-- Pure syntactic coverage of the current focus plus an exact-occurrence alias
class removes Joint. This permits arbitrary registries and prior installations.
The explicit path restriction is essential to the current-context transport. -/
theorem recorded_selected_joint (registry : Registry) (root focus : Occurrence roles)
    (context : Context) (state : State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) (initial context root) state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (atFocus : packet.site.occurrence = focus)
    (packetClass : ∀ prior ∈ state.packets,
      Alias state focus.identity prior.site.occurrence.identity → prior.site.occurrence = focus)
    (siteClass : ∀ site, Related state focus site → site.occurrence = focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    Joint registry state focus key := by
  have instanceRule := GeneralDictionaryCurrentJournal.initial_trace_current
    registry root context state path packet recorded model valid
  rw [atFocus] at instanceRule
  have branch := selected_branch registry state focus model packet.declaration.id key
    packet.children children instanceRule selected
  refine ⟨?_,model,valid,branch,?_⟩
  · intro prior member alias
    exact (GeneralDictionarySelectedInstanceCoherence.recorded_at_selected registry root focus
      context state path prior member (packetClass prior member alias) model valid key children selected).1
  · intro site related
    rw [siteClass site related]
    exact branch

end Yulang.GeneralDictionaryReachableEvidenceRecorded
