import Yulang.GeneralMixedDiagnosticHead304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticLocal304
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralMixedDiagnosticHead304
open GeneralMixedDiagnosticSlice304 (Semantics)
open CommonRoleOutermostResolver

variable {roles : Roles.RoleDecls} {a b : State roles}

abbrev boundary7 (roles : Roles.RoleDecls) := (boundary8 roles).toV7
abbrev boundary6 (roles : Roles.RoleDecls) := (boundary7 roles).toV6

theorem rejects6_forward (ab : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (given : B4TargetV6.RejectReason (boundary6 roles) reg a root) :
    B4TargetV6.RejectReason (boundary6 roles) reg b root := by
  obtain ⟨known,rootBad|candidateBad|⟨done,absent|⟨k,cs,choice,output⟩⟩⟩ := given
  · exact ⟨(not_congr (pending_iff ab reg root)).mp known,Or.inl ((root_k2_iff ab reg root).mp rootBad)⟩
  · exact ⟨(not_congr (pending_iff ab reg root)).mp known,
      Or.inr (Or.inl ((candidate_k2_iff ab reg root).mp candidateBad))⟩
  · refine ⟨(not_congr (pending_iff ab reg root)).mp known,Or.inr (Or.inr
      ⟨(not_congr (inspection_iff ab reg root)).mp done,Or.inl ?_⟩)⟩
    exact fun k cs seen => absent k cs ((survivor_iff ab reg root k cs).mpr seen)
  · exact ⟨(not_congr (pending_iff ab reg root)).mp known,Or.inr (Or.inr
      ⟨(not_congr (inspection_iff ab reg root)).mp done,Or.inr
        ⟨k,cs,unique_forward ab choice,output_forward ab output⟩⟩)⟩

theorem local6_forward (ab : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (given : B4TargetV6.Local (boundary6 roles) reg a root front) :
    B4TargetV6.Local (boundary6 roles) reg b root front := by
  cases given with
  | pending why => exact .pending ((pending_iff ab reg root).mp why)
  | inspectionPending known seen noRoot noCandidate =>
    exact .inspectionPending ((not_congr (pending_iff ab reg root)).mp known)
      ((inspection_iff ab reg root).mp seen) ((not_congr (root_k2_iff ab reg root)).mp noRoot)
      ((not_congr (candidate_k2_iff ab reg root)).mp noCandidate)
  | rejected why => exact .rejected (rejects6_forward ab reg root why)
  | ambiguous safe one two distinct =>
    exact .ambiguous (GeneralDeferredLadderAdministrative304.known_forward ab safe)
      ((survivor_iff ab reg root _ _).mp one) ((survivor_iff ab reg root _ _).mp two) distinct
  | selected safe unique noConflict =>
    exact .selected (GeneralDeferredLadderAdministrative304.known_forward ab safe)
      (unique_forward ab unique) ((not_congr (output_iff ab reg root _)).mp noConflict)

theorem priority_forward (ab : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (given : B4TargetV8.PriorityAmbiguity (boundary8 roles) reg a root) :
    B4TargetV8.PriorityAmbiguity (boundary8 roles) reg b root := by
  obtain ⟨okay,one,cs,two,ds,first,last,diff⟩ := given
  refine ⟨?_,one,cs,two,ds,(survivor_iff ab reg root one cs).mp first,
    (survivor_iff ab reg root two ds).mp last,diff⟩
  intro bad
  exact okay (((and_congr (not_congr (pending_iff ab reg root))
    (or_congr (root_k2_iff ab reg root) (candidate_k2_iff ab reg root))).mpr bad))

theorem priority_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    B4TargetV8.PriorityAmbiguity (boundary8 roles) reg a root ↔
      B4TargetV8.PriorityAmbiguity (boundary8 roles) reg b root :=
  ⟨priority_forward ab reg root,priority_forward ab.symm reg root⟩

theorem local7_iff (ab : HeadView a b) (slices : Semantics a b)
    (reg : Registry) (root : Occurrence roles) (front : Frontier (Occurrence roles)) :
    B4TargetV7.Local (boundary7 roles) reg a root front ↔
      B4TargetV7.Local (boundary7 roles) reg b root front :=
  B4TargetV7.local_transport (fun _ => ⟨local6_forward ab reg root,local6_forward ab.symm reg root⟩)
    (GeneralMixedDiagnosticSlice304.conflict_iff ab slices root) (priority_iff ab reg root) front

/-- The full concrete B4 local diagnostic factors through current head data
and the history-slice semantics. No history-list equality is required. -/
theorem local_iff (ab : HeadView a b) (slices : Semantics a b)
    (reg : Registry) (root : Occurrence roles) (front : Frontier (Occurrence roles)) :
    B4TargetV8.Local (boundary8 roles) reg a root front ↔
      B4TargetV8.Local (boundary8 roles) reg b root front :=
  B4TargetV8.local_transport (local7_iff ab slices reg root)
    (sharing_iff ab reg root) (priority_iff ab reg root) front

end Yulang.GeneralMixedDiagnosticLocal304
