import Yulang.GeneralDeclarativeStableCrossCompile329

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17500
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDeclarativeStableCrossBridge329
open GeneralDeclarativeStableCrossCompile329 (final chosen fallback compatible frame requested)
open GeneralDeclarativeStableCrossSource329 (actual keep spans)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeAggregate324 (ready aggregates span assembled)
open GeneralDeclarativeOpaqueGroup328 (aggregate_grows)
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeMerge320 (equality_sound)
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models)
open GeneralDeclarativeGrowth327 (Extends trans restrict ordinary)
open GeneralDeclarativeStableReplay329 (carry)
open GeneralDeclarativeRepeatedSource323 (registry parent goal)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeStableCompiler329 (Frame)
open CommonNominalFullCarrier (Equivalent subtype_refl common_union_is_join common_inter_is_meet)

abbrev start := tieState actual.state spans fallback
abbrev first := point 3
abbrev rest := [point 7]
abbrev before := aggregates start keep first rest
abbrev withFirst := ready start keep first rest

theorem prior_aggregate : Extends before final :=
  trans (ordinary _ _) (aggregate_grows withFirst keep first rest)

theorem aggregate_value (m) (fit : Models final m) :
    Equivalent (m 13).1 (m 3).1 ∧ Equivalent (m 14).1 (m 3).1 := by
  have merged := assembled (s := start) (extra := keep) (seed := first) (rest := rest)
    (fun a here => by
      rcases List.mem_cons.mp here with rfl|later
      · exact ⟨.refl _,.refl _⟩
      · cases List.mem_singleton.mp later
        exact ⟨.refl _,.refl _⟩)
  have lower := equality_sound merged.lowerEq m (restrict prior_aggregate m fit)
  have upper := equality_sound merged.upperEq m (restrict prior_aggregate m fit)
  change Equivalent (m 13).1 (.union (m 3).1 (m 7).1) at lower
  change Equivalent (m 14).1 (.inter (m 3).1 (m 7).1) at upper
  have same := compatible m fit
  have lo : Equivalent (.union (m 3).1 (m 7).1) (m 3).1 :=
    ⟨(common_union_is_join ..).mpr ⟨subtype_refl _,same.2⟩,
      ((common_union_is_join ..).mp (subtype_refl _)).1⟩
  have hi : Equivalent (.inter (m 3).1 (m 7).1) (m 3).1 :=
    ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
      (common_inter_is_meet ..).mpr ⟨subtype_refl _,same.1⟩⟩
  exact ⟨GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans lower lo,
    GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans upper hi⟩

abbrev bridge : List (PresenceNormalForm.Atom Nat) :=
  [.tyLe (.var 13) (.var 3),.tyLe (.var 3) (.var 13),
   .tyLe (.var 14) (.var 3),.tyLe (.var 3) (.var 14)]
abbrev current := withOrdinary final bridge

/-- Only the already supported scalar anchor plus selected tie is
used to expose a logical interval in this point-group regression.
The four additional named consequences preserve every model. -/
theorem conserves (m) : Models current m ↔ Models final m := by
  rw [ordinary_models]
  refine ⟨And.left,fun old => ⟨old,?_⟩⟩
  intro f included
  obtain ⟨lower,upper⟩ := aggregate_value m old
  simp only [bridge,List.mem_cons,List.not_mem_nil,or_false] at included
  rcases included with h|h|h|h <;> cases h
  · exact lower.1
  · exact lower.2
  · exact upper.1
  · exact upper.2

def compiled : Frame current registry interp goal parent [requested] :=
  carry frame (ordinary _ _)

theorem literal_alias (p : GeneralDeclarativeOrigins321.Supported current done) :
    GeneralDeclarativeLowerKnown321.Alias (GeneralDeclarativeOrigins321.restriction p) 13 3 :=
  .bounds (.constraint (List.mem_append_right _ List.mem_cons_self))
    (.constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))

end Yulang.GeneralDeclarativeStableCrossBridge329
