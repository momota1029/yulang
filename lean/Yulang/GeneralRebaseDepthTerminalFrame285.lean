import Yulang.GeneralRebaseDepthScalar285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 11500000
namespace Yulang.GeneralRebaseDepthTerminalFrame285
open GeneralDictionaryOutputDepth252 (snapshot plan model P initial registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseDepthScalar285 (old target refreshed fixed_models from_source new_zero new_one)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalOutputGrowth (tower tower_equivalent)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_refl subtype_trans)

theorem raw_source (m : Assignment) :
    GeneralNominalState.Models target.state m ↔ GeneralNominalState.Models snapshot m :=
  ⟨fun yes => ((GeneralNominalVersionedPlans231.private_models_iff _ _).mp
    ((GeneralNominalVersionedInstallation231.replay_private_models plan m).mp yes)).1,from_source m⟩

def rank (n : Nat) : Nat := if n ≤ 1 then 0 else if n = 3 then 3 else 1

theorem literal_depth (n : Nat) : (model n).1 = tower (rank n) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          have le : ¬ n.succ.succ.succ.succ ≤ 1 := by omega
          have ne : n.succ.succ.succ.succ ≠ 3 := by omega
          simp [rank,GeneralDictionaryOutputDepth252.model,GeneralDictionaryOutputDepth252.value,le,ne]
          rfl

theorem zero_one (one two : Nat) (same : rank one = rank two) (first : one ≤ 3) (last : two ≤ 3) :
    one = two ∨ (one ≤ 1 ∧ two ≤ 1) := by
  by_cases smallA : one ≤ 1
  · by_cases smallB : two ≤ 1
    · exact Or.inr ⟨smallA,smallB⟩
    · by_cases lastIs : two = 3 <;> simp [rank,smallA,smallB,lastIs] at same
  · by_cases smallB : two ≤ 1
    · by_cases firstIs : one = 3 <;> simp [rank,smallA,smallB,firstIs] at same
    · by_cases firstIs : one = 3 <;> by_cases lastIs : two = 3 <;> simp [rank,smallA,smallB,firstIs,lastIs] at same <;> omega

def putTop (n : Nat) : Assignment := fun k =>
  ((if k = n then .top else (model k).1),(model k).2)

theorem high_model (n : Nat) (large : 3 < n) : Models refreshed (putTop n) := by
  apply (fixed_models _).mpr
  apply (GeneralRebaseDepthGroundModels285.no_row_requirement model (putTop n) ?_).mp installed_model
  intro i initial
  have ne : i ≠ n := by omega
  simp [putTop,ne]

theorem not_top (n : Nat) : ¬ Equivalent .top (model n).1 := by
  rw [literal_depth]
  cases rank n with
  | zero => exact fun eq => GeneralNominalTopObservation.top_not_scalar .int eq.1
  | succ j => exact fun eq => GeneralNominalTopObservation.top_not_nominal 0 _ eq.1

theorem isolate_high (n m : Nat) (large : 3 < n) (distinct : n ≠ m) :
    ¬ GeneralNominalVersionedMixedKernel234.Equal refreshed n m := by
  intro same
  have witness := same _ (high_model n large)
  have other : m ≠ n := Ne.symm distinct
  simp only [putTop,ite_true,ite_eq_right other] at witness
  exact not_top m witness

theorem equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed refreshed := by
  intro a b _ _ full
  by_cases eq : a = b
  · subst b
    intro m _
    exact ⟨subtype_refl _,subtype_refl _⟩
  by_cases highA : 3 < a
  · exact (isolate_high a b highA eq full).elim
  by_cases highB : 3 < b
  · exact (isolate_high b a highB (Ne.symm eq) (fun m yes => ⟨(full m yes).2,(full m yes).1⟩)).elim
  have all : Models refreshed model := (fixed_models model).mpr installed_model
  have types := full model all
  rw [literal_depth a,literal_depth b] at types
  obtain same | low := zero_one a b ((tower_equivalent _ _).mp types)
    (by omega) (by omega)
  · subst b
    intro m _
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro m supports
    have raw := (GeneralRebaseDepthGroundModels285.source_inputs m).mp ((raw_source m).mp supports)
    have scalar (n : Nat) (small : n ≤ 1) : Equivalent (m n).1 GeneralDictionaryOutputDepth252.S := by
      have eq : n = 0 ∨ n = 1 := by omega
      rcases eq with rfl | rfl
      · exact raw.1
      · exact raw.2.1
    have one := scalar a low.1
    have two := scalar b low.2
    exact ⟨subtype_trans one.1 two.2,subtype_trans two.1 one.2⟩

theorem known_two : GeneralNominalState.Known target.state 2 := ⟨(2 : Fin 4),rfl,Or.inr ⟨_,rfl⟩⟩

theorem no_further_refresh (ctx : GeneralNominalCandidates.Context) (certificate : Refresh refreshed ctx)
    (n : Nat) (_present : n ∈ GeneralNominalState.sources target.state)
    (unknown : ¬ GeneralNominalState.Known target.state n) :
    ¬ GeneralNominalState.Known ctx.state n := by
  by_cases high : 3 < n
  · intro known
    obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have fact := GeneralNominalVersionedMixedObservations233.cache_sound certificate.cache
      (GeneralNominalSupport.head_recorded headed) (high_model n high)
    have shape := GeneralDictionaryGroundCopy218Refresh.head_holds headed fact
    simp only [putTop,ite_true] at shape
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test shape
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases possibilities with rfl|rfl|rfl|rfl
  · exact (unknown new_zero).elim
  · exact (unknown new_one).elim
  · exact (unknown known_two).elim
  · exact GeneralRebaseDepthScalar285.post_refresh_deep_not_known ctx.state certificate.cache

theorem point_closed : GeneralNominalReobservationSteps.PointClosed target.state := by
  intro slot desc found
  let slot4 : Fin 4 := slot
  have raw : (if slot4 = (2 : Fin 4) then some GeneralDictionaryOutputDepth252.foo else none) = some desc := found
  split at raw
  · have exactDesc := Option.some.inj raw
    subst desc
    intro param inside
    change param ∈ [GeneralNominalState.Parameter.type (((0 : Fin 4)),((0 : Fin 4)))] at inside
    cases List.mem_singleton.mp inside
    rfl
  · cases raw

end Yulang.GeneralRebaseDepthTerminalFrame285
