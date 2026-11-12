import Yulang.GeneralDictionaryCurrentJournal
/-! Exact-occurrence coherence in a common current context. Actual selection
provides the shared readiness/freshness guards; semantic Instance supplies its
own declaration-specific report and branch. No Joint premise is used. -/
namespace Yulang.GeneralDictionarySelectedInstanceCoherence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

/-- A semantic current instance must have the selected key and ordered children.
This is not alias transport: both judgments concern exactly the same occurrence. -/
theorem instance_selected (registry : Registry) (state : State roles)
    (root : Occurrence roles) (model : GeneralNominalCommonBridge.Assignment)
    (key selectedKey : Nat) (children selectedChildren : List (Occurrence roles))
    (instanceRule : Instance registry state.context model root key children)
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected selectedKey selectedChildren)) :
    key = selectedKey ∧ children = selectedChildren := by
  cases selected with
  | selected safe unique =>
    have guards := unique.1
    obtain ⟨_,chosen,_,chosenChecked,_,_,chosenBounds,_,chosenPrepared,_⟩ := guards
    obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := instanceRule
    have prepared : Prepared registry state.context root declaration checked :=
      ⟨metadata,chosenPrepared.2.1,chosenPrepared.2.2.1,bounds,located,finished,ready,model,branch⟩
    have survivor : Survivor registry state.context root key children :=
      ⟨safe.1,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩
    exact unique.2 key children survivor

/-- A recorded packet transported by the actual restricted initial trace agrees
with the final classifier at its exact occurrence, in any final journal model. -/
theorem recorded_selected (registry : Registry) (root : Occurrence roles)
    (context : Context) (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after packet.site.occurrence (.selected key children)) :
    packet.declaration.id = key ∧ packet.children = children :=
  instance_selected registry after packet.site.occurrence model packet.declaration.id key packet.children children
    (GeneralDictionaryCurrentJournal.initial_trace_current registry root context after path packet recorded model valid) selected

/-- Equality of occurrences is sufficient; no registry singleton restriction is needed. -/
theorem recorded_at_selected (registry : Registry) (root focus : Occurrence roles)
    (context : Context) (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (same : packet.site.occurrence = focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after focus (.selected key children)) :
    packet.declaration.id = key ∧ packet.children = children := by
  subst focus
  exact recorded_selected registry root context after path packet recorded model valid key children selected
end Yulang.GeneralDictionarySelectedInstanceCoherence
