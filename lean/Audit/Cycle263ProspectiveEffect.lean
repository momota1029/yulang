import Yulang.GeneralRebaseProspectiveEffect263
open Yulang
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalVersionedJournal232
example (registry : Registry) (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (demand : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
 ∃ plan : Plan roles, GeneralNominalVersionedEvidence231.Frame
 (GeneralNominalCenteredHeadAllocEncoding.registry registry) state.core demand key plan ∧
 GeneralNominalVersionedFrame231.children plan.packet = children := by
 obtain ⟨plan,frame,ordered,_⟩ := GeneralRebaseProspectiveEffect263.source_outcome registry root state reachable demand key children selected
 exact ⟨plan,frame,ordered⟩
#print axioms GeneralRebaseProspectiveEffect263.checked_effect
#print axioms GeneralRebaseProspectiveEffect263.source_frame_then_check
#print axioms GeneralRebaseProspectiveEffect263.source_outcome
