import Yulang.GeneralDeclarativeOpenFixtureSelection339
import Yulang.GeneralDeclarativeOpenTraversal339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 2400000
namespace Yulang.GeneralDeclarativeOpenFixtureModel339
open GeneralDeclarativeOpenFixtureBase339
open GeneralDeclarativeOpenFixtureRoutes339
open GeneralDeclarativeOpenFixtureSelection339
open GeneralDeclarativeCompoundTree338 (World advance fitsModel)
open GeneralDeclarativeCompoundInputs338 (input_exact)
open GeneralDeclarativeCompoundBatch338 (Ticket protectedNames)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeEndpointBatch336 (patch preserves)
open GeneralDeclarativeExactOverlay337 (ModelsExact values patch_checked list_sound)
open GeneralDeclarativeExactSupport337 (ready_after_ties receipts_same endpoints_sound)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeCompoundDictionary338 (Evidence)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent exactEmpty)

abbrev patchWorld := @GeneralDeclarativeOpenTraversal339.afterModel

theorem patch_world {w : World done} (t : Ticket w.source a f) (keep : List Nat) (m : Assignment)
    (fit : fitsModel w m) : fitsModel (advance w t keep) (patchWorld t keep m) :=
  (GeneralDeclarativeOpenExec339.execute t m fit keep).1

def seed1 : Assignment := patchWorld (w := w0) outerTicket keep before
def seed2 : Assignment := patchWorld (w := w1) innerTicket keep seed1
theorem seed_valid : fitsModel w2 seed2 :=
  patch_world (w := w1) innerTicket keep seed1
    (patch_world (w := w0) outerTicket keep before ⟨source_valid,fun _ h => False.elim (List.not_mem_nil h)⟩)

theorem root_values : (seed2 6).1 = (seed2 11).1 := rfl
theorem child_values : (seed2 5).1 = (seed2 14).1 := rfl
theorem exact_tail_values : (seed2 11).1 = exactEmpty ∧ (seed2 17).1 = exactEmpty := ⟨rfl,rfl⟩

theorem share_root (m) : EqualUses m used := by
  intro n x y first last
  simp only [used,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at first last
  rcases first with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases last with ⟨a,rfl⟩|⟨a,rfl⟩|⟨a,rfl⟩
  all_goals first | exact eqv_refl _ | contradiction

theorem share_child (m) : EqualUses m childUses := by
  intro n x y one two
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact eqv_refl _

theorem root_footprint : names w2.reads ⊆ stateNames (tieState w2.state used fallback) ++ keep := by
  have checked : (names w2.reads).all
      (fun n => decide (n ∈ stateNames (tieState w2.state used fallback) ++ keep)) = true := by decide +kernel
  intro n h; exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem child_footprint : names w2.reads ⊆ stateNames (tieState rootFinal childUses fallback) ++ keep := by
  have checked : (names w2.reads).all
      (fun n => decide (n ∈ stateNames (tieState rootFinal childUses fallback) ++ keep)) = true := by decide +kernel
  intro n h; exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem inhabited : ∃ m, ModelsExact final w2.reads m ∧ (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty := by
  obtain ⟨first,real,keepFirst⟩ := ready_after_ties (keep := keep) (fallback := fallback)
    seed_valid (share_root seed2) (input_exact GeneralDeclarativeOpenFixtureRoutes339.observed).2.2 root_footprint
  have rootModel : ModelsExact rootFinal w2.reads first := by
    refine ⟨(model_append _).mpr ⟨real.1,?_⟩,real.2⟩
    intro row active; cases List.mem_singleton.mp active
    change Equivalent (first 6).1 (first 11).1
    rw [keepFirst 6 (by decide +kernel),keepFirst 11 (by decide +kernel),root_values]
    exact eqv_refl _
  obtain ⟨last,child,keepLast⟩ := ready_after_ties (keep := keep) (fallback := fallback)
    rootModel (share_child first) (fun _ h => by cases List.mem_singleton.mp h; exact child_bounds) child_footprint
  refine ⟨last,⟨(model_append _).mpr ⟨child.1,?_⟩,child.2⟩,?_⟩
  · intro row active; cases List.mem_singleton.mp active
    change Equivalent (last 5).1 (last 14).1
    rw [keepLast 5 (by decide +kernel),keepLast 14 (by decide +kernel),
      keepFirst 5 (by decide +kernel),keepFirst 14 (by decide +kernel),child_values]
    exact eqv_refl _
  · rw [keepLast 11 (by decide +kernel),keepLast 17 (by decide +kernel),
      keepFirst 11 (by decide +kernel),keepFirst 17 (by decide +kernel)]
    exact exact_tail_values

/-- Neither node is vacuous: the genuinely elected nested root and
its emitted child both have dictionary evidence in one concrete model,
with both actual residual centers exactly closed after subtraction. -/
theorem verified_compound_dictionary :
    ∃ m, ModelsExact final w2.reads m ∧ (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty ∧
      Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit,a,b⟩ := inhabited
  exact ⟨m,fit,a,b,every_model m fit⟩

end Yulang.GeneralDeclarativeOpenFixtureModel339
