import Yulang.GeneralDeclarativeWitnessRowProjection334
import Yulang.GeneralDeclarativeWitnessJournalCase334
import Yulang.GeneralDeclarativeWitnessCompletion334

set_option backward.isDefEq.respectTransparency false
open Yulang
open GeneralDeclarativeWitnessRowProjection334
open GeneralDeclarativeWitnessJournalCase334
open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsResult332 (current)
open GeneralDeclarativeNestedSiblingsDecl332 (registry)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeWitnessFixture334 (waiting one_choice)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOrigins321 (backed_iff)
open GeneralDeclarativeWitnessReobserve334 (ReaderGrowth)

private theorem same_source_rows : Embeds firstHistorical (current noneDone) := by
  refine ⟨grow_two,?_⟩
  intro row seen
  obtain ⟨origin,fromHere,_⟩ := (backed_iff firstHistorical row).mp seen
  obtain ⟨part,rfl⟩ : row ∈ eqs ∧ origin = .source := fromHere
  exact (backed_iff (current noneDone) row).mpr ⟨.source,⟨part,rfl⟩,.source⟩

example : ¬ReaderGrowth firstHistorical (current noneDone) :=
  fun assumeMonotone => assumeMonotone.complete 100 rfl

example : Rule (current noneDone) registry interpretation waiting first (.selected leaf.id []) :=
  actual_selected same_source_rows historicalFirst (one_choice _)

namespace TrackedOutput
open GeneralDeclarativeWitnessCompletion334 (view before_back)
open GeneralDeclarativeWitnessCutBody334 (final opaqueCenter)
open GeneralDeclarativeWitnessCutRank334 (no_present_center)
open GeneralDeclarativeOrigins321 (from_completed)

/-- Same ordinary state is not enough when this very recorded origin
loses permission and no independent support for it remains. -/
theorem exact_gate (now : Nat → Prop) : Embeds (view (· = 100)) (view now) ↔ now 100 := by
  constructor
  · intro embedded
    apply Classical.byContradiction
    intro notYet
    have old := from_completed (view (· = 100)) (row := opaqueCenter)
      (Or.inr ⟨rfl,rfl⟩) rfl
    exact no_present_center ((before_back notYet).equations (embedded.available old))
  · intro ready
    exact origins_are_sufficient ⟨GeneralDeclarativeClauseBatch327.reflexive _,
      fun _ _ once => once,fun _ h => h.symm ▸ ready⟩

end TrackedOutput

#print axioms Yulang.GeneralDeclarativeWitnessRowProjection334.read_into_projected
#print axioms Yulang.GeneralDeclarativeWitnessRowProjection334.projected_into_now
#print axioms Yulang.GeneralDeclarativeWitnessRowProjection334.rebase
#print axioms Yulang.GeneralDeclarativeWitnessRowProjection334.actual_selected
#print axioms Yulang.GeneralDeclarativeWitnessRowProjection334.origins_are_sufficient
