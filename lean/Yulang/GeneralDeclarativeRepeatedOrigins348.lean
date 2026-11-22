import Yulang.GeneralDeclarativeRepeatedLayout348
import Yulang.GeneralDeclarativeRepeatedClosure348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 36000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeRepeatedOrigins348
open GeneralDeclarativeRepeatedLayout348 (rows written)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeRepeatedPlacement348 (keep placedView requested actual_placement)
open GeneralDeclarativeReplayCompile348 (output actual)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeInitialRoot343 (InputOrigin anchored origin_unique)
open GeneralDeclarativeOrigins321 (Supported restriction from_source from_completed backed_iff)
open GeneralDeclarativeGrowth327 (Extends trans facts)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWhereVersionInstall317 (fixed)
open GeneralWhereVersionCase317 (occ ordered_children)
open GeneralWhereVersionCompiler317 (children)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralDeclarativeRepeatedVisible348 (done completed)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralNominalSaturationState (Generated)

theorem output_extends : Extends (output keep) placedView := facts _ _

theorem printed_extends : Extends observedRoot placedView :=
  ⟨(by intro _ h; cases h),(by intro _ h; cases h),fun row h => by
    cases List.mem_singleton.mp h
    rw [written]
    exact List.mem_cons_self⟩

theorem source_print {row : Equation} (h : InputOrigin row) : row ∈ placedView.equations := by
  rw [origin_unique h,written]
  exact List.mem_cons_self

theorem child_print {row : Equation} (h : row ∈ rows) : row ∈ placedView.equations := by
  rw [written]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left [_] h))

/-- The emitted ordinary rows are not parser facts. Each is linked to
the actual current child and exact compiler recipe, behind a completed
transaction owner. No raw/ordinary RHS syntax identity is claimed. -/
structure ChildReceipt (row : Equation) : Prop where
  printed : row ∈ rows
  order : children rootPlan = [occ]
  generated : Generated fixed.mixed.core.erased.current root occ
  exactPlace : Placement fixed.mixed placedView occ requested

theorem child_receipt {row : Equation} (h : row ∈ rows) : ChildReceipt row := by
  obtain ⟨m,p⟩ := GeneralWhereVersionWitness317.inhabited
  have fit := (GeneralWhereVersionJournal317.fixed_iff m).mpr p
  exact ⟨h,ordered_children,GeneralWhereVersionInstall317.mixed_eq.symm ▸ GeneralWhereVersionCommit317.produced,
    actual_placement m fit⟩

def support {s : State} (g : Extends placedView s) : Supported s done :=
  ⟨fun row origin => (InputOrigin row ∧ origin = .source) ∨
      (ChildReceipt row ∧ origin = .output rootPlan.packet.site.occurrence.identity),fun found => by
    apply g.equations
    rcases found with h | h
    · exact source_print h.1
    · exact child_print h.1.printed⟩

theorem nominal_origin {s : State} (g : Extends placedView s) :
    publicRow ∈ (restriction (support g)).equations :=
  from_source _ (.inl ⟨anchored,rfl⟩)

theorem emitted_origin {s : State} (g : Extends placedView s) {row : Equation} (h : row ∈ rows) :
    row ∈ (restriction (support g)).equations :=
  from_completed _ (.inr ⟨child_receipt h,rfl⟩) completed

theorem no_promotion {s : State} (g : Extends placedView s) {row : Equation} :
    (support g).derivesFrom row .source → row = publicRow := by
  rintro (⟨h,_⟩|⟨_,h⟩)
  · exact origin_unique h
  · cases h

def rootSlice {s : State} (g : Extends placedView s) :
    GeneralDeclarativeWitnessHead334.Slice (support g) :=
  ⟨observedRoot,GeneralDeclarativeInitialRoot343.support done,trans printed_extends g,
    ⟨(by intro _ h; cases h),(by intro _ h; cases h),fun row present => by
      obtain ⟨origin,fromHere,_⟩ := (backed_iff _ _).mp present
      rw [origin_unique fromHere.1]
      exact nominal_origin g⟩⟩

noncomputable def childSlice {s : State} (g : Extends placedView s) :
    GeneralDeclarativeWitnessHead334.Slice (support g) :=
  ⟨placedView,support (reflexive _),g,⟨g.constraints,g.intervals,fun row present => by
    obtain ⟨origin,h,valid⟩ := (backed_iff _ _).mp present
    exact (backed_iff _ _).mpr ⟨origin,h,valid⟩⟩⟩

end Yulang.GeneralDeclarativeRepeatedOrigins348
