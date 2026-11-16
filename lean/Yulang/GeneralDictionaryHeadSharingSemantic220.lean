import Yulang.GeneralDictionaryHeadSharingBoundary220

/-! Sharing is diagnosed only after ordinary head readiness. In particular it
cannot consume a V7 pending or ambiguous result. -/
namespace Yulang.GeneralDictionaryHeadSharingSemantic220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
open GeneralDictionaryHeadSharingConflict220 (Conflict)
variable {roles : Roles.RoleDecls}

theorem conflict_safe (bad : Conflict (roles := roles) value state focus) :
    B4TargetV7.SafeKnown (GeneralDictionaryDefaultBoundary208.boundary roles) value state focus := by
  obtain ⟨_,_,_,safe,_⟩ := bad
  exact safe

theorem pending_not_conflict
    (old : GeneralDictionaryDefaultBoundary208.Local (roles := roles) value state focus .pending) :
    ¬ Conflict value state focus := by
  intro bad
  have safe := conflict_safe bad
  cases old with
  | ordinary _ prior =>
    cases prior with
    | pending pending => exact safe.1 pending
    | inspectionPending _ pending _ _ => exact safe.2.2.2 pending

theorem pending_iff_prior : Local (roles := roles) value state focus .pending ↔
    GeneralDictionaryDefaultBoundary208.Local value state focus .pending := by
  constructor
  · intro selected
    exact (B4TargetV8.pending_iff.mp selected).1
  · intro old
    exact .ordinary (pending_not_conflict old) old

theorem ambiguous_not_conflict
    (old : GeneralDictionaryDefaultBoundary208.Local (roles := roles) value state focus .ambiguous) :
    ¬ Conflict value state focus := by
  rintro ⟨key,children,unique,_,_⟩
  cases old with
  | ordinary _ prior =>
    cases prior with
    | ambiguous _ one two different =>
      exact B4TargetV3.unique_not_ambiguous unique one two different
  | mergedAmbiguous _ ambiguity => exact B4TargetV7.unique_not_priorityAmbiguity unique ambiguity

theorem ambiguous_iff_prior : Local (roles := roles) value state focus .ambiguous ↔
    GeneralDictionaryDefaultBoundary208.Local value state focus .ambiguous := by
  constructor
  · intro chosen
    cases chosen with
    | ordinary _ old => exact old
    | sharingAmbiguous conflict ambiguity =>
      obtain ⟨_,_,unique,_,_⟩ := conflict
      exact False.elim (B4TargetV8.unique_not_priorityAmbiguity unique ambiguity)
  · intro old
    exact .ordinary (ambiguous_not_conflict old) old

/-- Old rejection reasons are never removed by the new sharing diagnostic. -/
theorem rejected_of_prior
    (old : GeneralDictionaryDefaultBoundary208.Local (roles := roles) value state focus .rejected) :
    Local value state focus .rejected := by
  classical
  by_cases bad : Conflict value state focus
  · exact GeneralDictionaryHeadSharingBoundary220.conflict_rejected bad
  · exact .ordinary bad old

/-- Exactly the old rejections plus the newly specified sharing contradictions. -/
theorem rejected_iff_prior_or_conflict : Local (roles := roles) value state focus .rejected ↔
    GeneralDictionaryDefaultBoundary208.Local value state focus .rejected ∨ Conflict value state focus := by
  constructor
  · intro rejected
    cases rejected with
    | ordinary _ old => exact Or.inl old
    | sharingRejected bad _ => exact Or.inr bad
  · rintro (old | bad)
    · exact rejected_of_prior old
    · exact GeneralDictionaryHeadSharingBoundary220.conflict_rejected bad

/-- A previously selected head is rejected precisely when its sharing is contradictory. -/
theorem selected_rejected_iff_conflict
    (old : GeneralDictionaryDefaultBoundary208.Local (roles := roles) value state focus (.selected key children)) :
    Local value state focus .rejected ↔ Conflict value state focus := by
  constructor
  · intro rejected
    rcases rejected_iff_prior_or_conflict.mp rejected with rejected | bad
    · have impossible := B4TargetV7.local_functional old rejected
      cases impossible
    · exact bad
  · exact GeneralDictionaryHeadSharingBoundary220.conflict_rejected

end Yulang.GeneralDictionaryHeadSharingSemantic220
