import Yulang.GeneralDeclarativeWitnessSeparateEndpointAuthors362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 70000
set_option maxHeartbeats 76000000
namespace Yulang.GeneralDeclarativeWitnessSeparateAuthorModel362
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run payload)
open GeneralDeclarativeWitnessNativeThreeModel362 (copies)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact exact_model_iff)
open GeneralDeclarativeWitnessRecordWidthFixture359 (current)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews no_ordinary_override)
open GeneralDeclarativeWitnessNativePreparation360 (same_model_of_prepared)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype subtype_refl)
open PresenceNormalForm (Atom)

def rows (contra : Bool) : List (Atom Nat) :=
  ((copies (payload contra 0) 304 305 ++ copies (payload contra 1) 306 307) ++ copies (payload contra 2) 308 309).map
    fun xy => .tyLe (.var xy.1) (.var xy.2)

def state (contra : Bool) : State :=
  ⟨⟨current.normal.ordinary ++ rows contra,current.normal.intervals⟩,current.equations⟩

def known {contra} (x : Ordered contra) := exact x.after.final.ordinary (state contra)

theorem actual_ordered_snapshot (contra : Bool) :
    ((run contra).map known).getD false = true := by cases contra <;> decide +kernel

def model (contra u : Bool) : Assignment := fun n =>
  let old := GeneralDeclarativeWitnessRecordWidthFixture359.model u
  if n = 304 ∨ n = 305 then old (payload contra 0)
  else if n = 306 ∨ n = 307 then old (payload contra 1)
  else if n = 308 ∨ n = 309 then old (payload contra 2)
  else old n

theorem fits_state (contra u : Bool) : Models (state contra) (model contra u) := by
  let old := GeneralDeclarativeWitnessRecordWidthFixture359.model u
  have fresh : (stateNames current).all
      (fun n => decide (n ≠ 304 ∧ n ≠ 305 ∧ n ≠ 306 ∧ n ≠ 307 ∧ n ≠ 308 ∧ n ≠ 309)) = true := by decide +kernel
  have eq (n : Nat) (used : n ∈ stateNames current) : old n = model contra u n := by
    obtain ⟨a,b,c,d,e,f⟩ := of_decide_eq_true (List.all_eq_true.mp fresh n used)
    simp [model,old,a,b,c,d,e,f]
  have preserved := (preserves_models _ eq).mp (GeneralDeclarativeWitnessRecordWidthFixture359.model_fits u)
  refine ⟨⟨?_,preserved.1.2⟩,preserved.2⟩
  intro a stored
  rcases (List.mem_append.mp stored : a ∈ current.normal.ordinary ∨ a ∈ rows contra) with known|new
  · exact preserved.1.1 a known
  · cases contra <;>
      simp only [rows,copies,payload,GeneralDeclarativeWitnessThreeNative362.first,
        GeneralDeclarativeWitnessThreeNative362.last,
        Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,
        List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    all_goals rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact subtype_refl _

theorem every_fit_of_third_author_keeps_original_window {contra} (x : Ordered contra)
    (m : Assignment) (v : NativeViews) (fit : Fits x.after.final m v) :
    Models current m ∧ Subtype (m 60).1 (m 61).1 ∧ Subtype (m 61).1 (m 62).1 := by
  have firstLift := no_ordinary_override x.after.prepared x.after.native x.after.installed ▸ fit.1
  have sourceTwo : Models x.center.final.ordinary m := (same_model_of_prepared x.after.prepared m firstLift).1
  have secondLift := no_ordinary_override x.center.prepared x.center.native x.center.installed ▸ sourceTwo
  have sourceOne : Models x.before.final.ordinary m := (same_model_of_prepared x.center.prepared m secondLift).1
  have thirdLift := no_ordinary_override x.before.prepared x.before.native x.before.installed ▸ sourceOne
  have old : Models current m := (same_model_of_prepared x.before.prepared m thirdLift).1
  exact ⟨old,old.1.1 (.tyLe (.var 60) (.var 61)) (by decide +kernel),
    old.1.1 (.tyLe (.var 61) (.var 62)) (by decide +kernel)⟩

theorem actual_multi_owner_model (contra : Bool) :
    ∃ x : Ordered contra, run contra = some x ∧
      ∀ u, Fits x.after.final (model contra u) (interpreted x.after.final.board (model contra u)) := by
  have checked := actual_ordered_snapshot contra
  cases filled : run contra with
  | none => rw [filled] at checked; cases checked
  | some x =>
    rw [filled] at checked
    exact ⟨x,rfl,fun u =>
      ⟨(exact_model_iff (show known x = true from checked) _).mpr (fits_state contra u),fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessSeparateAuthorModel362
