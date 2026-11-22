import Yulang.GeneralDeclarativeEndpointChildren336
import Yulang.GeneralDeclarativeEndpointConserve336

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeEndpointChildModels336
open GeneralDeclarativeEndpointChildren336
open GeneralDeclarativeRecordDecl326 (registry)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEndpointOverlay336 (ModelsWith values patch_checked)
open GeneralDeclarativeEndpointBatch336 (patch)
open GeneralDeclarativeEndpointConserve336 (names ready_after_ties)
open GeneralDeclarativeEndpointDictionary336 (Evidence)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeEndpointSupport336 (materialize)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record exactEmpty emptyRecord mask subtype_refl common_record_mono exactEmpty_below_width)

def sourceModel : Assignment := fun n =>
  (if n = 0 ∨ n = 1 then record 7 int exactEmpty else
    if n = 2 then record 7 int emptyRecord else
    if n = 6 then mask [7] (record 7 int exactEmpty) else int,Common.rowEmpty)

theorem source_valid : Models initial sourceModel := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e used
    change e ∈ [(0,1),(1,2)] at used
    rcases List.mem_cons.mp used with rfl|tail
    · exact subtype_refl _
    · cases List.mem_singleton.mp tail
      exact common_record_mono 7 (subtype_refl _) exactEmpty_below_width
  · intro row used
    change row ∈ [lo,hi,scalar] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl <;> exact eqv_refl _

def seed : Assignment := patch initial keep (values sourceModel jobs) sourceModel

theorem seed_valid : ModelsWith named sidecar seed :=
  patch_checked sourceModel source_valid
    ((GeneralDeclarativeEndpointProgram336.list_sound GeneralDeclarativeEndpointChildren336.read program).2 sourceModel source_valid) protect

theorem shared_root (m : Assignment) : EqualUses m uses := by
  intro name a b one two
  rw [uses_eq] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at one two
  rcases one with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases two with ⟨same,rfl⟩|⟨same,rfl⟩
  all_goals first | exact eqv_refl _ | contradiction

theorem shared_child (m : Assignment) : EqualUses m childUses := by
  intro n a b one two
  have one' := List.mem_singleton.mp one
  have two' := List.mem_singleton.mp two
  cases one'
  cases two'
  exact eqv_refl _

theorem footprint_root : names sidecar ⊆ stateNames (tieState named uses fallback) ++ protect := by
  have checked : (names sidecar).all
      (fun n => decide (n ∈ stateNames (tieState named uses fallback) ++ protect)) = true := by decide +kernel
  intro n h
  exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem footprint_child : names sidecar ⊆ stateNames (tieState rootFinal childUses fallback) ++ protect := by
  have checked : (names sidecar).all
      (fun n => decide (n ∈ stateNames (tieState rootFinal childUses fallback) ++ protect)) = true := by decide +kernel
  intro n h
  exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem inhabited : ∃ m, ModelsWith final sidecar m := by
  obtain ⟨first,valid,kept⟩ := ready_after_ties (keep := protect) (fallback := fallback)
    seed_valid (shared_root seed) (fun _ found => GeneralDeclarativeEndpointOverlay336.spans_ready found) footprint_root
  have first_valid : ModelsWith rootFinal sidecar first := by
    refine ⟨(model_append _).mpr ⟨valid.1,?_⟩,valid.2⟩
    intro e used
    cases List.mem_singleton.mp used
    change CommonNominalFullCarrier.Equivalent (first 6).1 (first 11).1
    rw [kept 6 (by decide +kernel),kept 11 (by decide +kernel)]
    exact eqv_refl _
  obtain ⟨last,validLast,keptLast⟩ := ready_after_ties (keep := protect) (fallback := fallback)
    first_valid (shared_child first) (fun _ found => by cases List.mem_singleton.mp found; exact child_bounds) footprint_child
  have childModel : ModelsWith childFinal sidecar last := by
    refine ⟨(model_append _).mpr ⟨validLast.1,?_⟩,validLast.2⟩
    intro e used
    cases List.mem_singleton.mp used
    change CommonNominalFullCarrier.Equivalent (last 5).1 (last 8).1
    rw [keptLast 5 (by decide +kernel),keptLast 8 (by decide +kernel),
      kept 5 (by decide +kernel),kept 8 (by decide +kernel)]
    exact eqv_refl _
  exact ⟨last,(materialize childFinal sidecar last).mpr childModel⟩

/-- Exact I-61 mixed-tail parent, generated ordinary child, both real
fixed writes, and inhabited same-model two-node dictionary. -/
theorem recursively_checked :
    ∃ m, ModelsWith final sidecar m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨m,fit,every_model m fit⟩

end Yulang.GeneralDeclarativeEndpointChildModels336
