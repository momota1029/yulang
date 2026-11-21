import Yulang.GeneralWhereOriginConfig318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 29000000
namespace Yulang.GeneralWhereOriginFixture318
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (sourceRegistry otherChild boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralWhereVersionCase317 (lower upper lowerRow upperRow expr)
open GeneralWhereVersionBase317 (injectOld loSlot hiSlot source_old source_lo source_hi lower_fresh upper_fresh new_cases)
open GeneralWhereVersionSnapshot317 (context snap)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereOriginDelta318 (Cell Delta High)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (variables)
open GeneralWhereVersionRootReport317 (plan)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralWhereOriginConfig318 (already_holds)

noncomputable def lowerCell : Cell rootPlan :=
  ⟨otherChild,0,.lower,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,
    (fun _ eq => by cases eq),rfl⟩
noncomputable def upperCell : Cell rootPlan :=
  ⟨otherChild,0,.upper,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,
    (fun _ eq => by cases eq),rfl⟩

theorem initial_trace : Trace sourceRegistry before := by
  apply Trace.legacy after
  rintro i ⟨k,tag,eq⟩
  exact GeneralVersionedHighOrigins315.raw_absent reachable tag
    (eq ▸ GeneralNominalAllocationSupport.slot_source raw i)

noncomputable def real_delta : Delta raw snap rootPlan where
  refinement := GeneralWhereVersionRefine317.refines
  current := rfl
  cells := [lowerCell,upperCell]
  absent := by
    intro c belongs
    rcases List.mem_cons.mp belongs with rfl|other
    · exact lower_fresh
    · cases List.mem_singleton.mp other
      exact upper_fresh
  fresh_slot := by
    intro c belongs
    rcases List.mem_cons.mp belongs with rfl|other
    · exact ⟨loSlot,source_lo⟩
    · cases List.mem_singleton.mp other
      exact ⟨hiSlot,source_hi⟩
  split_slot := by
    intro i _
    refine Fin.addCases (m := 8) (n := 2) ?_ ?_ i
    · intro j
      exact Or.inl ⟨j,source_old j⟩
    · intro j
      rcases new_cases j with rfl|rfl
      · exact Or.inr ⟨lowerCell,List.mem_cons_self,source_lo⟩
      · exact Or.inr ⟨upperCell,List.mem_cons_of_mem _ (List.mem_singleton_self _),source_hi⟩

theorem actual_trace : Trace sourceRegistry fixed :=
  .placed context rootPlan initial_trace GeneralWhereVersionInstall317.step real_delta

noncomputable def lowerCurrent : Cell plan :=
  ⟨otherChild,0,.lower,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,
    (fun _ eq => by cases eq),rfl⟩
noncomputable def upperCurrent : Cell plan :=
  ⟨otherChild,0,.upper,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,
    (fun _ eq => by cases eq),rfl⟩

theorem authoritative_config (m : Assignment) (valid : Models fixed m) :
    lowerCurrent.row.Holds (variables plan m) m ∧ upperCurrent.row.Holds (variables plan m) m := by
  have parent := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  have frame := GeneralWhereVersionRootHead317.frame m parent
  have fits : GeneralNominalVersionedEvidence231.Frame
    (GeneralVersionedHistoryEvidence310.Compiled sourceRegistry) fixed.mixed.core
    root GeneralLiveCompoundRegistry316.declaration.id plan := by
    rw [GeneralWhereVersionInstall317.mixed_eq]
    exact frame
  refine ⟨already_holds boundary_checked actual_trace fits lowerCurrent (i := loSlot) ?_ m valid,
    already_holds boundary_checked actual_trace fits upperCurrent (i := hiSlot) ?_ m valid⟩
  · change sourceSlot snap.base _ = some loSlot
    exact GeneralWhereVersionReuse317.exact_slots.1
  · change sourceSlot snap.base _ = some hiSlot
    exact GeneralWhereVersionReuse317.exact_slots.2

end Yulang.GeneralWhereOriginFixture318
