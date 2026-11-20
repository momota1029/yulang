import Yulang.GeneralMixedIndexedPlanSemantics305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedDiagnosticHeads305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralMixedIndexedFrame305
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralNominalVersionedCycles232 (RootCycle CandidateCycle full_models_only)
open GeneralDeferredLadderOperationalView304 (alias_forward)
open GeneralNominalVersionedCandidates231 (inputs)
variable {roles : Roles.RoleDecls} {a b : State roles}

theorem model_eq (s : IndexedView a b) : Models a = Models b :=
  funext fun m => propext (s.raw.models m)

theorem admin_forward (s : IndexedView a b) (old : AdministrativeReady a root) :
    AdministrativeReady b root := by
  unfold AdministrativeReady at old ⊢
  rw [s.centers] at old
  refine ⟨old.1,?_⟩
  intro first one loc second two eq
  rw [← model_eq s] at eq
  exact alias_forward s.raw (old.2 first one loc second two eq)

theorem root_cycle_forward (s : IndexedView a b) (cycle : RootCycle a root) :
    RootCycle b root := by
  rcases cycle with ⟨index,found⟩|⟨site,member,eq,index,found⟩
  · exact Or.inl ⟨index,(full_models_only (model_eq s)).mp found⟩
  · exact Or.inr ⟨site,s.centers ▸ member,eq,index,(full_models_only (model_eq s)).mp found⟩

theorem candidate_cycle_forward (s : IndexedView a b) (cycle : CandidateCycle r a root) :
    CandidateCycle r b root := by
  obtain ⟨p,f,position,listed,cyclic⟩ := cycle
  refine ⟨relocate s f,relocated_frame s f,position,?_,(full_models_only (model_eq s)).mp cyclic⟩
  change position ∈ (GeneralNominalCenteredSteps.inspection
    (GeneralNominalReportContext305.movePlan p (coordinates s f))).tests
  rwa [inspected_tests (coordinates s f)]

theorem pending_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    (boundary8 roles).RootPending r a root ↔ (boundary8 roles).RootPending r b root :=
  GeneralNominalCandidateReplayModels305.pending_iff s.ctx (inputs root)

theorem root_k2_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    (boundary8 roles).RootK2 r a root ↔ (boundary8 roles).RootK2 r b root :=
  or_congr (GeneralNominalK2Coordinates305.root_iff s.ctx (inputs root).demand)
    ⟨root_cycle_forward s,root_cycle_forward (reverse s)⟩

theorem candidate_k2_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    (boundary8 roles).CandidateK2 r a root ↔ (boundary8 roles).CandidateK2 r b root :=
  or_congr (GeneralNominalK2Coordinates305.candidate_iff s.ctx r (inputs root))
    ⟨candidate_cycle_forward s,candidate_cycle_forward (reverse s)⟩

theorem inspection_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    (boundary8 roles).InspectionPending r a root ↔ (boundary8 roles).InspectionPending r b root :=
  or_congr (GeneralNominalVersionedCandidateCoordinates305.inspection_pending_iff s.ctx r root)
    (not_congr ⟨admin_forward s,admin_forward (reverse s)⟩)

theorem survivor_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) :
    (boundary8 roles).Survivor r a root key children ↔ (boundary8 roles).Survivor r b root key children :=
  GeneralNominalVersionedCandidateCoordinates305.survivor_iff s.ctx r root key children

theorem unique_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) :
    B4TargetV8.Unique (boundary8 roles) r a root key children ↔
      B4TargetV8.Unique (boundary8 roles) r b root key children :=
  GeneralNominalVersionedCandidateCoordinates305.unique_iff s.ctx r root key children

theorem safe_iff (s : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    B4TargetV8.SafeKnown (boundary8 roles) r a root ↔ B4TargetV8.SafeKnown (boundary8 roles) r b root :=
  and_congr (not_congr (pending_iff s r root))
    (and_congr (not_congr (root_k2_iff s r root))
      (and_congr (not_congr (candidate_k2_iff s r root))
        (not_congr (inspection_iff s r root))))

end Yulang.GeneralMixedIndexedDiagnosticHeads305
