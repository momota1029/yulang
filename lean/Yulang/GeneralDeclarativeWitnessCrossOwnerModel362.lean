import Yulang.GeneralDeclarativeWitnessCrossOwnerReceiver362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 75000
set_option maxHeartbeats 88000000
namespace Yulang.GeneralDeclarativeWitnessCrossOwnerModel362
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (Consumed consume check)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact exact_model_iff)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def rows : List (Atom Nat) :=
  [(302,302),(302,302),(310,301),(301,310),(311,303),(303,311),(310,302),(302,311),
   (61,61),(61,61),(312,60),(60,312),(313,62),(62,313),(312,61),(61,313),
   (302,302),(302,302),(314,310),(310,314),(315,311),(311,315),(314,302),(302,315)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def stage (contra : Bool) : State :=
  let original := GeneralDeclarativeWitnessSeparateAuthorModel362.state contra
  ⟨⟨original.normal.ordinary ++ rows,original.normal.intervals⟩,original.equations⟩

def checkState {contra x} (w : @Consumed contra x) : Bool := exact w.reader.world.ordinary (stage contra)

theorem actual_multi_owner_reader_state (contra : Bool) :
    ((run contra).bind fun x => (consume x).map checkState).getD false = true := by
  cases contra <;> decide +kernel

def model (contra u : Bool) : Assignment := fun n =>
  let old := GeneralDeclarativeWitnessSeparateAuthorModel362.model contra u
  if n = 310 ∨ n = 314 then old 301
  else if n = 311 ∨ n = 315 then old 303
  else if n = 312 then old 60
  else if n = 313 then old 62
  else old n

theorem fits_current (contra u : Bool) : Models (stage contra) (model contra u) := by
  let old := GeneralDeclarativeWitnessSeparateAuthorModel362.model contra u
  let prior := GeneralDeclarativeWitnessSeparateAuthorModel362.state contra
  have new : (stateNames prior).all (fun n =>
      decide (n ≠ 310 ∧ n ≠ 311 ∧ n ≠ 312 ∧ n ≠ 313 ∧ n ≠ 314 ∧ n ≠ 315)) = true := by
    cases contra <;> decide +kernel
  have same (n : Nat) (active : n ∈ stateNames prior) : old n = model contra u n := by
    obtain ⟨a,b,c,d,e,f⟩ := of_decide_eq_true (List.all_eq_true.mp new _ active)
    simp [model,old,a,b,c,d,e,f]
  have retained := (preserves_models prior same).mp (GeneralDeclarativeWitnessSeparateAuthorModel362.fits_state contra u)
  refine ⟨⟨?_,retained.1.2⟩,retained.2⟩
  intro a stored
  rcases (List.mem_append.mp stored : a ∈ prior.normal.ordinary ∨ a ∈ rows) with known|internal
  · exact retained.1.1 _ known
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at internal
    rcases internal with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases u <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem actual_common_fitted_state_from_three_authors (contra : Bool) :
    ∃ (x : Ordered contra) (w : Consumed x), run contra = some x ∧ consume x = some w ∧
      check w = true ∧
      ∀ u,Fits w.reader.world (model contra u) (interpreted w.reader.world.board (model contra u)) := by
  have checked := actual_multi_owner_reader_state contra
  have claims := GeneralDeclarativeWitnessCrossOwnerReceiver362.actual_read_of_three_independent_sources contra
  cases began : run contra with
  | none => rw [began] at checked; cases checked
  | some x =>
    rw [began] at checked claims
    change ((consume x).map checkState).getD false = true at checked
    change ((consume x).map check).getD false = true at claims
    cases read : consume x with
    | none => rw [read] at checked; cases checked
    | some w =>
      rw [read] at checked claims
      exact ⟨x,w,rfl,read,claims,fun u =>
        ⟨(exact_model_iff (show checkState w = true from checked) _).mpr (fits_current contra u),fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessCrossOwnerModel362
