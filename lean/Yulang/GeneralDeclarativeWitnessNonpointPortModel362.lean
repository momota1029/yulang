import Yulang.GeneralDeclarativeWitnessNonpointPort362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 70000
set_option maxHeartbeats 74000000
namespace Yulang.GeneralDeclarativeWitnessNonpointPortModel362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessNonpointPort362 (Transport forward view)
open GeneralDeclarativeWitnessNativeThreeModel362 (copies after model fits_after)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open PresenceNormalForm (Atom)

def rows : List (Atom Nat) :=
  [(202,202),(202,202),(210,201),(201,210),(211,203),(203,211),(210,202),(202,211),
   (61,61),(61,61),(212,60),(60,212),(213,62),(62,213),(212,61),(61,213)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def stage (contra : Bool) : State :=
  let prior := after contra
  ⟨⟨prior.normal.ordinary ++ rows,prior.normal.intervals⟩,prior.equations⟩

def exact (s t : State) : Bool :=
  decide (s.normal.ordinary = t.normal.ordinary ∧ s.normal.intervals = t.normal.intervals ∧ s.equations = t.equations)

theorem exact_model_iff {s t : State} (shown : exact s t = true) (m : Assignment) : Models s m ↔ Models t m := by
  have same := of_decide_eq_true shown
  constructor <;> intro f
  · exact ⟨⟨fun row h => f.1.1 row (same.1.symm ▸ h),fun row h => f.1.2 row (same.2.1.symm ▸ h)⟩,
      fun row h => f.2 row (same.2.2.symm ▸ h)⟩
  · exact ⟨⟨fun row h => f.1.1 row (same.1 ▸ h),fun row h => f.1.2 row (same.2.1 ▸ h)⟩,
      fun row h => f.2 row (same.2.2 ▸ h)⟩

def exactWorld {contra r gate} (p : @Transport contra r gate) : Bool := exact p.world.ordinary (stage contra)

theorem actual_state_after_emission (contra : Bool) :
    ((run contra).bind fun r => (forward r authority).map exactWorld).getD false = true := by
  cases contra <;> decide +kernel

def extended (contra u : Bool) : Assignment := fun n =>
  if n = 210 then model contra u 201
  else if n = 211 then model contra u 203
  else if n = 212 then model contra u 60
  else if n = 213 then model contra u 62
  else model contra u n

theorem extended_fits (contra u : Bool) : Models (stage contra) (extended contra u) := by
  have fresh : (stateNames (after contra)).all
      (fun a => decide (a ≠ 210 ∧ a ≠ 211 ∧ a ≠ 212 ∧ a ≠ 213)) = true := by cases contra <;> decide +kernel
  have same (n : Nat) (used : n ∈ stateNames (after contra)) : model contra u n = extended contra u n := by
    obtain ⟨n0,n1,n2,n3⟩ := of_decide_eq_true (List.all_eq_true.mp fresh n used)
    simp [extended,n0,n1,n2,n3]
  have old := (preserves_models _ same).mp (fits_after contra u)
  refine ⟨⟨?_,old.1.2⟩,old.2⟩
  intro row used
  rcases (List.mem_append.mp used : row ∈ (after contra).normal.ordinary ∨ row ∈ rows) with known|new
  · exact old.1.1 row known
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases u <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem actual_nonpoint_child_one_model_family (contra : Bool) :
    ∃ (r : Run contra) (p : Transport r authority),
      run contra = some r ∧ forward r authority = some p ∧
      ∀ u, Fits p.world (extended contra u) (interpreted p.world.board (extended contra u)) := by
  have h := actual_state_after_emission contra
  cases made : run contra with
  | none => rw [made] at h; cases h
  | some r =>
    rw [made] at h
    change ((forward r authority).map exactWorld).getD false = true at h
    cases child : forward r authority with
    | none => rw [child] at h; cases h
    | some p =>
      rw [child] at h
      exact ⟨r,p,rfl,child,fun u => ⟨(exact_model_iff (show exactWorld p = true from h) _).mpr (extended_fits contra u),fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessNonpointPortModel362
