import Yulang.GeneralDeclarativeWitnessNestedFixture361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 63000
set_option maxHeartbeats 61000000
namespace Yulang.GeneralDeclarativeWitnessNestedModel361
open GeneralDeclarativeWitnessNestedFixture361 (CheckedLeaf start close full nestedHead)
open GeneralDeclarativeWitnessNestedLeaf361 (Local classified)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativePortTransport361 (Part view every_projected_endpoint_is_the_released_value)
open GeneralDeclarativeWitnessNativeNestedMatch361 (Meaning values independent_match_sound)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)
open CommonRoleOutermostResolver (Classify)

def tailAtoms : List (Atom Nat) :=
  [(61,61),(61,61),(116,106),(106,116),(117,107),(107,117),(116,61),(61,117)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def state : State :=
  let s := GeneralDeclarativeWitnessSequentialNative360.final
  ⟨⟨s.normal.ordinary ++ tailAtoms,s.normal.intervals⟩,s.equations⟩

def exact {negative r s} (x : @CheckedLeaf negative r s) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same x.result.world.ordinary state

theorem actual_compiler_keeps_the_payload_interval (negative : Bool) :
    ((start negative false).bind fun r => (sequence r).bind fun s =>
      (close s).map exact).getD false = true := by
  cases negative <;> decide +kernel

def model (upper : Bool) (scalar : Inference.Base) : Assignment := fun n =>
  if n = 116 then GeneralDeclarativeWitnessSequentialNative360.model upper scalar 106
  else if n = 117 then GeneralDeclarativeWitnessSequentialNative360.model upper scalar 107
  else GeneralDeclarativeWitnessSequentialNative360.model upper scalar n

theorem model_fits (upper : Bool) (scalar : Inference.Base) : Models state (model upper scalar) := by
  let prev := GeneralDeclarativeWitnessSequentialNative360.final
  let old := GeneralDeclarativeWitnessSequentialNative360.model upper scalar
  have a16 : 116 ∉ stateNames prev := by decide +kernel
  have a17 : 117 ∉ stateNames prev := by decide +kernel
  have agrees (n : Nat) (used : n ∈ stateNames prev) : old n = model upper scalar n := by
    have h16 : n ≠ 116 := fun h => a16 (h ▸ used)
    have h17 : n ≠ 117 := fun h => a17 (h ▸ used)
    simp [model,old,h16,h17]
  have kept := (preserves_models prev agrees).mp
    (GeneralDeclarativeWitnessSequentialNative360.ordered_model upper scalar)
  refine ⟨⟨?_,kept.1.2⟩,kept.2⟩
  intro row there
  rcases (List.mem_append.mp there : row ∈ prev.normal.ordinary ∨ row ∈ tailAtoms) with old|new
  · exact kept.1.1 _ old
  · simp only [tailAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem composed_leaf_sound {negative} {r : Run negative} {s : Sequence r}
    (p : CheckedLeaf s) (m : Assignment) (v : NativeViews) (fit : Fits p.result.world m v) :
    Classify (Local p.origin) s.receiver (.selected (.node p.chosen.impl.id [])) ∧
    (∀ which : Part, ∃ seen,view p.origin v which = some seen ∧
      Meaning r.env seen p.chosen.pattern (values m p.chosen.captures)) ∧
    p.result.prep.impl = p.chosen.impl ∧ p.result.body.kids = [] ∧ p.result.body.fixed = [] := by
  have prior : Fits s.final m v :=
    ⟨restrict ((preserves_iff ..).mp p.result.kept) m fit.1,fit.2⟩
  refine ⟨classified p.chosen,?_,p.result.sameDecl,p.result.noKids,p.result.noWrites⟩
  intro which
  exact ⟨_,every_projected_endpoint_is_the_released_value p.origin m v prior which,
    independent_match_sound p.chosen.matchInput m⟩

theorem actual_nested_dictionary_in_one_fitted_model (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r) (p : CheckedLeaf s),
      start negative false = some r ∧ sequence r = some s ∧ close s = some p ∧
      full s p = true ∧
      (∀ upper scalar,Fits p.result.world (model upper scalar) (interpreted p.result.world.board (model upper scalar))) ∧
      (∀ m v,Fits p.result.world m v →
        Classify (Local p.origin) s.receiver (.selected (.node p.chosen.impl.id [])) ∧
        (∀ which : Part, ∃ seen,view p.origin v which = some seen ∧
          Meaning r.env seen p.chosen.pattern (values m p.chosen.captures)) ∧
        Holds m ⟨105,.variable 61⟩) := by
  have h := actual_compiler_keeps_the_payload_interval negative
  have shapes := GeneralDeclarativeWitnessNestedFixture361.actual_nested_binder_does_not_use_nominal_address negative
  cases root : start negative false with
  | none => rw [root] at h; cases h
  | some r =>
    rw [root] at h shapes
    change ((sequence r).bind fun s => (close s).map exact).getD false = true at h
    change ((sequence r).bind fun s => (close s).map (full s)).getD false = true at shapes
    cases sent : sequence r with
    | none => rw [sent] at h; cases h
    | some s =>
      rw [sent] at h shapes
      change ((close s).map exact).getD false = true at h
      change ((close s).map (full s)).getD false = true at shapes
      cases ran : close s with
      | none => rw [ran] at h; cases h
      | some p =>
        rw [ran] at h shapes
        have same := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show exact p = true from h)
        refine ⟨r,s,p,rfl,sent,ran,shapes,fun u k => ⟨same.symm ▸ model_fits u k,fun _ => rfl⟩,?_⟩
        intro m v fit
        have rule := composed_leaf_sound p m v fit
        refine ⟨rule.1,rule.2.1,?_⟩
        have base := fit.1.2
        rw [same] at base
        exact base _ (List.mem_append_right _ (by decide +kernel))

end Yulang.GeneralDeclarativeWitnessNestedModel361
