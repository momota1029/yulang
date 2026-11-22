import Yulang.GeneralDeclarativeNativeReplay347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeNativeRepeatStage347
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeNativeReplay347 (keep)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeStableAssemble329 (merged tieState assemble witness_projection)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeInitialModels343 (singleton_bounds)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeGrowth327 (restrict fits)
open GeneralDeclarativeAggregate324 (span ready assembled ready_iff)
open GeneralDeclarativeMerge320 (equality_sound)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev spans : List (Nat × Capture) := [(0,typePoint),(0,typePoint)]
def fallback (_ : Nat) : Capture := typePoint
noncomputable abbrev phase := (merged observedRoot keep spans fallback).state
noncomputable abbrev capture := (merged observedRoot keep spans fallback).captures
noncomputable abbrev tied := tieState observedRoot spans fallback

theorem ranges : ∀ e ∈ spans, Bounds observedRoot e.2 := by
  intro e present
  rcases List.mem_cons.mp present with rfl|rest
  · exact point_bounded _ _
  · cases List.mem_singleton.mp rest
    exact point_bounded _ _

theorem compatible (m : Assignment) : EqualUses m spans := by
  intro k a b ha hb
  have atPoint (u : Capture) (present : (k,u) ∈ spans) : u = typePoint := by
    rcases List.mem_cons.mp present with same|rest
    · exact congrArg Prod.snd same
    · exact congrArg Prod.snd (List.mem_singleton.mp rest)
  rw [atPoint a ha,atPoint b hb]
  exact eqv_refl _

theorem common (m : Assignment) (fit : Models observedRoot m) :
    ∃ n, Models phase n ∧ ∀ k ∈ keep, n k = m k := by
  obtain ⟨n,valid,held⟩ := (witness_projection (assemble keep spans fallback ranges) m).mp ⟨fit,compatible m⟩
  exact ⟨n,valid,fun k used => held k (List.mem_append_right _ used)⟩

theorem group : GeneralDeclarativeOpaqueGroup328.group 0 spans = [typePoint,typePoint] := rfl

theorem exact_capture : capture 0 = span tied keep typePoint [typePoint] := rfl

theorem exact_phase : phase = ready (ready tied keep typePoint [typePoint]) keep typePoint [typePoint] := rfl

theorem chosen_bound : Bounds phase (capture 0) := by
  have made := (assemble keep spans fallback ranges).ranges (0,typePoint) List.mem_cons_self
  exact made

theorem actual_modes (m : Assignment) (fit : Models phase m) :
    Equivalent (m (capture 0).lower).1 (m 2).1 ∧
    (capture 0).center = 2 ∧
    Equivalent (m (capture 0).upper).1 (m 2).1 := by
  rw [exact_phase] at fit
  have front : Models (ready tied keep typePoint [typePoint]) m :=
    restrict (GeneralDeclarativeOpaqueGroup328.aggregate_grows _ _ _ _) m fit
  have all : ∀ a ∈ [typePoint,typePoint], Bounds tied a := by
    intro a h
    rcases List.mem_cons.mp h with rfl|rest
    · exact point_bounded _ _
    · cases List.mem_singleton.mp rest
      exact point_bounded _ _
  have printed := assembled (s := tied) (extra := keep) (seed := typePoint) (rest := [typePoint]) all
  have atoms := ((ready_iff (extra := keep) all m).mp front)
  have lo := equality_sound printed.lowerEq m atoms
  have hi := equality_sound printed.upperEq m atoms
  rw [exact_capture]
  change Equivalent (m (span tied keep typePoint [typePoint]).lower).1 (m 2).1 ∧
    (span tied keep typePoint [typePoint]).center = 2 ∧
    Equivalent (m (span tied keep typePoint [typePoint]).upper).1 (m 2).1
  let t := (m 2).1
  have hInter : Equivalent (.inter t t) t := by
    refine ⟨?_,(CommonNominalFullCarrier.common_inter_is_meet t t t).mpr
      ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩
    exact ((CommonNominalFullCarrier.common_inter_is_meet t t (.inter t t)).mp
      (CommonNominalFullCarrier.subtype_refl _)).1
  exact ⟨GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans lo
      (GeneralDeclarativePlainCapture323.union_same t),rfl,
    GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans hi hInter⟩

end Yulang.GeneralDeclarativeNativeRepeatStage347
