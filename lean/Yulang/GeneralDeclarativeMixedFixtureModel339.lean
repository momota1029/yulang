import Yulang.GeneralDeclarativeMixedFixtureSelection339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 2400000
namespace Yulang.GeneralDeclarativeMixedFixtureModel339
open GeneralDeclarativeMixedFixtureBase339
open GeneralDeclarativeMixedFixtureRoutes339
open GeneralDeclarativeMixedFixtureSelection339
open GeneralDeclarativeCompoundTree338 (fitsModel footprint)
open GeneralDeclarativeMixedInputs339 (input_exact)
open GeneralDeclarativeOpenTraversal339 (afterModel)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeExactSupport337 (ready_after_ties)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeMixedDictionary339 (Evidence)
open GeneralDeclarativeDemand320 (bounds_sound)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans)
open CommonNominalFullCarrier (Equivalent exactEmpty)
open GeneralNominalCommonBridge (Assignment)

def seed1 : Assignment := afterModel (w := w0) outerTicket keep before
def seed2 : Assignment := afterModel (w := w1) innerTicket keep seed1

theorem seed_actual : fitsModel w2 seed2 :=
  (GeneralDeclarativeOpenExec339.execute innerTicket seed1
    (GeneralDeclarativeOpenExec339.execute outerTicket before
      ⟨source_valid,fun _ h => False.elim (List.not_mem_nil h)⟩ keep).1 keep).1

theorem root_value : (seed2 6).1 = (seed2 11).1 := rfl
theorem scalar_value : (seed2 5).1 = (seed2 3).1 := rfl

theorem share_root (m) : EqualUses m used := by
  intro n x y first last
  simp only [used,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at first last
  rcases first with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases last with ⟨a,rfl⟩|⟨a,rfl⟩|⟨a,rfl⟩
  all_goals first | exact eqv_refl _ | contradiction

theorem share_child (m) : EqualUses m childUses := by
  intro _ _ _ a b; cases List.mem_singleton.mp a; cases List.mem_singleton.mp b; exact eqv_refl _

theorem root_footprint : names w3.reads ⊆ stateNames (tieState w3.state used fallback) ++ keep := by
  have checked : (names w3.reads).all
      (fun n => decide (n ∈ stateNames (tieState w3.state used fallback) ++ keep)) = true := by decide +kernel
  intro n h; exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem child_footprint : names w3.reads ⊆ stateNames (tieState rootFinal childUses fallback) ++ keep := by
  have checked : (names w3.reads).all
      (fun n => decide (n ∈ stateNames (tieState rootFinal childUses fallback) ++ keep)) = true := by decide +kernel
  intro n h; exact of_decide_eq_true (List.all_eq_true.mp checked n h)

theorem modeled : ∃ m, ModelsExact final w3.reads m ∧ (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty := by
  obtain ⟨afterLeaf,fitLeaf,keptLeaf⟩ := (GeneralDeclarativeCompoundInputs338.old_sound sourceLeaf).2 seed2 seed_actual
  have actualScalar := bounds_sound ((GeneralDeclarativeMixedTree339.exact_tree leafActual).2.2
    (0,payloadArg) List.mem_cons_self) afterLeaf fitLeaf.1
  obtain ⟨afterRoot,fitRoot,keptRoot⟩ := ready_after_ties (keep := keep) (fallback := fallback)
    fitLeaf (share_root afterLeaf) (input_exact GeneralDeclarativeMixedFixtureRoutes339.observed).2.2 root_footprint
  have withRoot : ModelsExact rootFinal w3.reads afterRoot := by
    refine ⟨(model_append _).mpr ⟨fitRoot.1,?_⟩,fitRoot.2⟩
    intro row used; cases List.mem_singleton.mp used
    change Equivalent (afterRoot 6).1 (afterRoot 11).1
    rw [keptRoot 6 (by decide +kernel),keptRoot 11 (by decide +kernel),
        keptLeaf 6 (by decide +kernel),keptLeaf 11 (by decide +kernel),root_value]
    exact eqv_refl _
  obtain ⟨afterChild,fitChild,keptChild⟩ := ready_after_ties (keep := keep) (fallback := fallback)
    withRoot (share_child afterRoot) (fun _ h => by cases List.mem_singleton.mp h; exact child_bounds) child_footprint
  refine ⟨afterChild,⟨(model_append _).mpr ⟨fitChild.1,?_⟩,fitChild.2⟩,?_⟩
  · intro row used; cases List.mem_singleton.mp used
    change Equivalent (afterChild 5).1 (afterChild 19).1
    rw [keptChild 5 (by decide +kernel),keptChild 19 (by decide +kernel),
      keptRoot 5 (by decide +kernel),keptRoot 19 (by decide +kernel),keptLeaf 5 (by decide +kernel),scalar_value,
      ← keptLeaf 3 (by decide +kernel)]
    exact ⟨actualScalar.1,actualScalar.2⟩
  · rw [keptChild 11 (by decide +kernel),keptChild 17 (by decide +kernel),
        keptRoot 11 (by decide +kernel),keptRoot 17 (by decide +kernel),
        keptLeaf 11 (by decide +kernel),keptLeaf 17 (by decide +kernel)]
    exact ⟨rfl,rfl⟩

/-- The existing elected variant located inside two record fields
truly emits the child and both fixed outputs in one model. Neither
the outer record nor the variant center needed a source RHS. -/
theorem actual_mixed_dictionary :
    ∃ m, ModelsExact final w3.reads m ∧
      (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty ∧
      Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit,a,b⟩ := modeled
  exact ⟨m,fit,a,b,every_model m fit⟩

end Yulang.GeneralDeclarativeMixedFixtureModel339
