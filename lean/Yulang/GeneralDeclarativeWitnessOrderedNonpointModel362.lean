import Yulang.GeneralDeclarativeWitnessOrderedNonpointRepeat362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 74000
set_option maxHeartbeats 84000000
namespace Yulang.GeneralDeclarativeWitnessOrderedNonpointModel362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority ctor first last)
open GeneralDeclarativeWitnessOrderedNonpointRepeat362 (PairOfBodies produce exact)
open GeneralDeclarativeWitnessNonpointReceiver362 (fitting fitting_state)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact_model_iff)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessCompiler350 (trip)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def rows : List (Atom Nat) :=
  [(202,202),(202,202),(216,210),(210,216),(217,211),(211,217),(216,202),(202,217)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def after (contra : Bool) : State :=
  let prior := GeneralDeclarativeWitnessNonpointReceiver362.state contra
  ⟨⟨prior.normal.ordinary ++ rows,prior.normal.intervals⟩,prior.equations⟩

def checkState {contra r} (w : @PairOfBodies contra r) : Bool :=
  GeneralDeclarativeWitnessNonpointPortModel362.exact w.last.world.ordinary (after contra)

theorem actual_both_returns_keep_source_state (contra : Bool) :
    ((run contra).bind fun r => (produce r).map checkState).getD false = true := by cases contra <;> decide +kernel

def model (contra u : Bool) : Assignment := fun n =>
  if n = 216 then fitting contra u 210 else if n = 217 then fitting contra u 211 else fitting contra u n

theorem model_after_both (contra u : Bool) : Models (after contra) (model contra u) := by
  let prior := GeneralDeclarativeWitnessNonpointReceiver362.state contra
  have fresh : (stateNames prior).all (fun n => decide (n ≠ 216 ∧ n ≠ 217)) = true := by cases contra <;> decide +kernel
  have same (n : Nat) (known : n ∈ stateNames prior) : fitting contra u n = model contra u n := by
    obtain ⟨a,b⟩ := of_decide_eq_true (List.all_eq_true.mp fresh _ known)
    simp [model,a,b]
  have old := (preserves_models prior same).mp (fitting_state contra u)
  refine ⟨⟨?_,old.1.2⟩,old.2⟩
  intro row included
  rcases (List.mem_append.mp included : row ∈ prior.normal.ordinary ∨ row ∈ rows) with backed|internal
  · exact old.1.1 row backed
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at internal
    rcases internal with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem exact_source_after_two_children {contra} {r : Run contra} (initial : run contra = some r)
    (w : PairOfBodies r) (m : Assignment) (v : NativeViews) (fit : Fits w.last.world m v) :
    v 201 = some (.unary (ctor contra) (.leaf (m (first contra)).1)) ∧
    v 202 = some (.unary (ctor contra) (.leaf (m 61).1)) ∧
    v 203 = some (.unary (ctor contra) (.leaf (m (last contra)).1)) := by
  have one := restrict ((preserves_iff ..).mp w.last.keeps) m fit.1
  have two := restrict ((preserves_iff ..).mp w.first.keeps) m one
  have three := (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared w.parent m two).1
  exact GeneralDeclarativeWitnessOrderedNativeRelease362.source_code_in_every_fit initial w.granted m v ⟨three,fit.2⟩

theorem two_children_have_exact_same_model (contra : Bool) :
    ∃ (r : Run contra) (w : PairOfBodies r), run contra = some r ∧ produce r = some w ∧
      trip w.first.span = (214,202,215) ∧ trip w.last.span = (216,202,217) ∧
      ∀ u, Fits w.last.world (model contra u) (interpreted w.last.world.board (model contra u)) := by
  have h := actual_both_returns_keep_source_state contra
  have spans := GeneralDeclarativeWitnessOrderedNonpointRepeat362.actual_two_scopes_share_exact_center_not_alias_addresses contra
  cases source : run contra with
  | none => rw [source] at h; cases h
  | some r =>
    rw [source] at h spans
    change ((produce r).map checkState).getD false = true at h
    change ((produce r).map exact).getD false = true at spans
    cases made : produce r with
    | none => rw [made] at h; cases h
    | some out =>
      rw [made] at h spans
      have known := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (show exact out = true from spans)).1).1).1
      exact ⟨r,out,rfl,made,known.2.2.1,known.2.2.2,fun u =>
        ⟨(exact_model_iff (show checkState out = true from h) _).mpr (model_after_both contra u),fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessOrderedNonpointModel362
