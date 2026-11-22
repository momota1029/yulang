import Yulang.GeneralDeclarativeFrameGuard343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15200
set_option maxHeartbeats 6700000
namespace Yulang.GeneralDeclarativeCurrentOrigins343
open GeneralDeclarativeFrameShape343 (grows source_ordinary output_ordinary childRows)
open GeneralDeclarativePlacement343 (view)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (output child)
open GeneralDeclarativeInitialRoot343 (InputOrigin anchored)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeOrigins321 (Supported restriction from_source from_completed)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralDeclarativeVersionedPhysical342 (current actual_children recorded_version)
open GeneralNominalSaturationState (Generated)

def done (name : Nat) : Prop := name = root.identity ∧ plan ∈ final.versionedWhere

theorem completed : done root.identity := ⟨rfl,recorded_version⟩

/-- Exact correspondence of the source compiler's own emitted child
and the independently produced current physical occurrence. These
are not exported as new literal parser rows. -/
structure ChildReceipt (row : Equation) : Prop where
  printed : row ∈ childRows
  order : GeneralWhereVersionCompiler317.children current = [newChild.occurrence]
  committed : newChild ∈ final.mixed.core.sites
  generated : Generated final.mixed.core.erased.current root newChild.occurrence
  currentCompiler : GeneralDeclarativeNestedBody332.compileBody
    GeneralWhereOriginSingleSource318.sourceRegistry GeneralDictionaryJournalRefinement228Source.interpretation
    GeneralDeclarativeVersionedRootGuard342.actualDemand GeneralWhereOriginSingleSource318.declaration
    observedRoot GeneralDeclarativeVersionedRootShape342.spans kept
    GeneralDeclarativeLogicalChild343.fallback GeneralDeclarativeLogicalChild343.targets =
      some (output kept,[child kept])
  placement : GeneralDeclarativeStoppedPaired341.Placement final.mixed view newChild.occurrence (child kept)

theorem recorded {row : Equation} (used : row ∈ childRows) : ChildReceipt row :=
  ⟨used,actual_children,GeneralDeclarativeVersionedPhysical342.new_registered,GeneralWherePhysicalCommit319.produced,
    GeneralDeclarativeOrdinary343.actual kept,GeneralDeclarativePlacement343.actual_place⟩

def support {s : State} (advance : Extends view s) : Supported s done :=
  ⟨fun row origin => (InputOrigin row ∧ origin = .source) ∨
    (ChildReceipt row ∧ origin = .output root.identity),fun known => by
      apply advance.equations
      rcases known with left | right
      · exact source_ordinary _ left.1
      · exact output_ordinary _ right.1.printed⟩

theorem nominal_origin {s : State} (advance : Extends view s) :
    publicRow ∈ (restriction (support advance)).equations :=
  from_source _ (.inl ⟨anchored,rfl⟩)

theorem emitted_origin {s : State} (advance : Extends view s) {row : Equation} (here : row ∈ childRows) :
    row ∈ (restriction (support advance)).equations :=
  from_completed _ (.inr ⟨recorded here,rfl⟩) completed

theorem no_promotion {s : State} (advance : Extends view s) {row : Equation} :
    (support advance).derivesFrom row .source → row = publicRow := by
  rintro (⟨a,_⟩|⟨_,no⟩)
  · exact GeneralDeclarativeInitialRoot343.origin_unique a
  · cases no

def rootSlice {s : State} (advance : Extends view s) :
    GeneralDeclarativeWitnessHead334.Slice (support advance) :=
  ⟨observedRoot,GeneralDeclarativeInitialRoot343.support done,trans grows advance,
    ⟨(by intro _ h; cases h),(by intro _ h; cases h),fun row present => by
      obtain ⟨origin,fromHere,_⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp present
      have isRow := GeneralDeclarativeInitialRoot343.origin_unique fromHere.1
      rw [isRow]
      exact nominal_origin advance⟩⟩

noncomputable def childSlice {s : State} (advance : Extends view s) :
    GeneralDeclarativeWitnessHead334.Slice (support advance) :=
  ⟨view,support (reflexive view),advance,⟨advance.constraints,advance.intervals,
    fun row present => by
      obtain ⟨origin,old,available⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp present
      exact (GeneralDeclarativeOrigins321.backed_iff _ _).mpr ⟨origin,old,available⟩⟩⟩

end Yulang.GeneralDeclarativeCurrentOrigins343
