import Yulang.GeneralMixedDiagnosticSlice304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticHead304
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralDeferredLadderResnapshot304 (HeadView ready_forward)
open GeneralDeferredLadderOperationalView304 (classes_iff frame_forward)
open GeneralDeferredLadderAdministrative304
open GeneralNominalVersionedDiagnostic232
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {a b : State roles}

abbrev boundary8 (roles : Roles.RoleDecls) := GeneralNominalVersionedDiagnostic232.boundary roles

theorem pending_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    (boundary8 roles).RootPending reg a root ↔ (boundary8 roles).RootPending reg b root := by
  change GeneralNominalState.RootPending a.core.erased.current.context.state _ ↔
    GeneralNominalState.RootPending b.core.erased.current.context.state _
  rw [ab.context]

theorem root_k2_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    (boundary8 roles).RootK2 reg a root ↔ (boundary8 roles).RootK2 reg b root := by
  change (_ ∨ GeneralNominalVersionedCycles232.RootCycle a root) ↔
    (_ ∨ GeneralNominalVersionedCycles232.RootCycle b root)
  refine or_congr ?_ ⟨root_cycle_backward ab.symm,root_cycle_backward ab⟩
  change GeneralNominalCycleK2.RootK2 a.core.erased.current.context.state _ ↔
    GeneralNominalCycleK2.RootK2 b.core.erased.current.context.state _
  rw [ab.context]

theorem candidate_k2_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    (boundary8 roles).CandidateK2 reg a root ↔ (boundary8 roles).CandidateK2 reg b root := by
  change (_ ∨ GeneralNominalVersionedCycles232.CandidateCycle reg a root) ↔
    (_ ∨ GeneralNominalVersionedCycles232.CandidateCycle reg b root)
  refine or_congr ?_ ⟨candidate_cycle_backward ab.symm,candidate_cycle_backward ab⟩
  change GeneralNominalVersionedCycles232.RawCandidateK2 reg a.core.erased.current.context _ ↔
    GeneralNominalVersionedCycles232.RawCandidateK2 reg b.core.erased.current.context _
  rw [ab.context]

theorem inspection_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    (boundary8 roles).InspectionPending reg a root ↔ (boundary8 roles).InspectionPending reg b root := by
  change (_ ∨ ¬ AdministrativeReady a root) ↔ (_ ∨ ¬ AdministrativeReady b root)
  refine or_congr ?_ (not_congr ⟨administrative_forward ab,administrative_forward ab.symm⟩)
  change GeneralNominalVersionedCandidates231.InspectionPending reg a.core.erased.current.context root ↔
    GeneralNominalVersionedCandidates231.InspectionPending reg b.core.erased.current.context root
  rw [ab.context]

theorem survivor_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) :
    (boundary8 roles).Survivor reg a root key children ↔
      (boundary8 roles).Survivor reg b root key children := by
  change GeneralNominalVersionedCandidates231.Survivor reg a.core.erased.current.context root key children ↔
    GeneralNominalVersionedCandidates231.Survivor reg b.core.erased.current.context root key children
  rw [ab.context]

theorem chosen_head_forward (ab : HeadView a b) (given : ChosenHead reg a root key m) :
    ChosenHead reg b root key m := by
  obtain ⟨⟨cs,okay⟩,p,frame,ready,head⟩ := given
  exact ⟨⟨cs,ab.context ▸ okay⟩,p,frame_forward ab.raw ab.context ab.centers frame,
    ready_forward ab ready,head⟩

theorem chosen_effect_forward (ab : HeadView a b) (given : ChosenEffects reg a root key m) :
    ChosenEffects reg b root key m := by
  obtain ⟨⟨cs,okay⟩,p,frame,ready,head,effects⟩ := given
  exact ⟨⟨cs,ab.context ▸ okay⟩,p,frame_forward ab.raw ab.context ab.centers frame,
    ready_forward ab ready,head,(classes_iff ab.raw p root m).mp effects⟩

theorem output_forward (ab : HeadView a b) (given : OutputConflict reg a root key) :
    OutputConflict reg b root key := by
  obtain ⟨⟨m,ma,head⟩,no⟩ := given
  refine ⟨⟨m,(ab.raw.models m).mp ma,chosen_head_forward ab head⟩,?_⟩
  rintro ⟨m,mb,effects⟩
  exact no ⟨m,(ab.raw.models m).mpr mb,chosen_effect_forward ab.symm effects⟩

theorem output_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) (key : Nat) :
    OutputConflict reg a root key ↔ OutputConflict reg b root key :=
  ⟨output_forward ab,output_forward ab.symm⟩

theorem feasible_forward (ab : HeadView a b) (given : Feasible reg a root key) :
    Feasible reg b root key := by
  obtain ⟨m,valid,p,frame,sharing⟩ := given
  exact ⟨m,(ab.raw.models m).mp valid,p,frame_forward ab.raw ab.context ab.centers frame,sharing⟩

theorem at_key_forward (ab : HeadView a b) (given : AtKey reg a root key) :
    AtKey reg b root key := by
  obtain ⟨⟨m,valid⟩,⟨p,frame⟩,no⟩ := given
  exact ⟨⟨m,(ab.raw.models m).mp valid⟩,⟨p,frame_forward ab.raw ab.context ab.centers frame⟩,
    fun found => no (feasible_forward ab.symm found)⟩

theorem unique_forward (ab : HeadView a b)
    (given : B4TargetV8.Unique (boundary8 roles) reg a root key children) :
    B4TargetV8.Unique (boundary8 roles) reg b root key children :=
  ⟨(survivor_iff ab reg root key children).mp given.1,
    fun other kids seen => given.2 other kids ((survivor_iff ab reg root other kids).mpr seen)⟩

theorem sharing_forward (ab : HeadView a b) (given : SharingConflict reg a root) :
    SharingConflict reg b root := by
  obtain ⟨key,kids,unique,safe,clash⟩ := given
  exact ⟨key,kids,unique_forward ab unique,known_forward ab safe,at_key_forward ab clash⟩

theorem sharing_iff (ab : HeadView a b) (reg : Registry) (root : Occurrence roles) :
    SharingConflict reg a root ↔ SharingConflict reg b root :=
  ⟨sharing_forward ab,sharing_forward ab.symm⟩

end Yulang.GeneralMixedDiagnosticHead304
