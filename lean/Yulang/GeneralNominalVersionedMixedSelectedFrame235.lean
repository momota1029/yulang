import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralNominalVersionedMixedFrameSelection235
set_option backward.isDefEq.respectTransparency false
/-! Actual selected current frames from reachable raw/centered registration.
No full packet or shared journal model is assumed to build this frame. -/
namespace Yulang.GeneralNominalVersionedMixedSelectedFrame235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {state : State roles}

theorem administrative_ready
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children)) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady state demand := by
  classical
  exact Classical.byContradiction (fun absent =>
    (GeneralNominalVersionedMixedCurrentCandidate235.selected_safe selected).2.2.2 (Or.inr absent))

theorem source_frame
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
    ∃ plan, GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core demand key plan ∧ GeneralNominalVersionedFrame231.children plan.packet = children := by
  have chosen := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected
  obtain ⟨center,recorded,centerEq⟩ := (administrative_ready chosen).1
  obtain ⟨raw,rawRecorded,rawEq⟩ := GeneralNominalVersionedMixedTrace235.centered_registered path recorded
  have rawFocus := rawEq.trans centerEq
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique chosen
  obtain ⟨known,declaration,visible,checked,keyEq,role,bounds,located,prepared,childrenEq⟩ := unique.1
  let packet : GeneralNominalSaturationState.Packet roles :=
    ⟨GeneralNominalCenteredHeadAllocEncoding.registry registry,state.core.erased.current.context,raw,declaration,checked,bounds⟩
  let plan : Plan roles := ⟨packet,center,rawEq.symm⟩
  have frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core demand key plan :=
    ⟨rfl,rfl,rawFocus,keyEq,rawRecorded,recorded,visible,role,located,prepared⟩
  exact ⟨plan,frame,(GeneralNominalVersionedMixedFrameSelection235.selected_identifies chosen frame).2⟩

end Yulang.GeneralNominalVersionedMixedSelectedFrame235
