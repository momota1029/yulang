import Yulang.GeneralDeclarativeWitnessTwoChildDictionary363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 84000
set_option maxHeartbeats 108000000
namespace Yulang.GeneralDeclarativeWitnessTwoChildModel363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessTwoActualChildren363 (Pair build checked two_distinct_ordered_literal_children)
open GeneralDeclarativeWitnessTwoChildDictionary363 (Local Meaning actual_ordered_sibling_dict actual_sibling_dict_same_model)
open GeneralDeclarativeWitnessTwoActualChildren363 (Leaf)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (rootQuery)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact exact_model_iff)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open CommonRoleOutermostResolver (Classify)
open PresenceNormalForm (Atom)

def rows : List (Atom Nat) :=
  [(302,302),(302,302),(316,310),(310,316),(317,311),(311,317),(316,302),(302,317)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def stage (contra : Bool) : State :=
  let old := GeneralDeclarativeWitnessCrossOwnerModel362.stage contra
  ⟨⟨old.normal.ordinary ++ rows,old.normal.intervals⟩,old.equations⟩

def model (contra u : Bool) : Assignment := fun n =>
  let old := GeneralDeclarativeWitnessCrossOwnerModel362.model contra u
  if n = 316 then old 310 else if n = 317 then old 311 else old n

theorem model_fits_both_scopes (contra u : Bool) : Models (stage contra) (model contra u) := by
  let old := GeneralDeclarativeWitnessCrossOwnerModel362.model contra u
  let prior := GeneralDeclarativeWitnessCrossOwnerModel362.stage contra
  have fresh : (stateNames prior).all (fun n => decide (n ≠ 316 ∧ n ≠ 317)) = true := by
    cases contra <;> decide +kernel
  have same (n : Nat) (active : n ∈ stateNames prior) : old n = model contra u n := by
    obtain ⟨a,b⟩ := of_decide_eq_true (List.all_eq_true.mp fresh n active)
    simp [model,old,a,b]
  have retained := (preserves_models prior same).mp (GeneralDeclarativeWitnessCrossOwnerModel362.fits_current contra u)
  refine ⟨⟨?_,retained.1.2⟩,retained.2⟩
  intro a stored
  rcases (List.mem_append.mp stored : a ∈ prior.normal.ordinary ∨ a ∈ rows) with before|after
  · exact retained.1.1 _ before
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at after
    rcases after with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases u <;> first | exact subtype_refl _ | exact endpoints_ordered

def verified {contra x} (p : @Pair contra x) : Bool :=
  checked p && exact p.b.world.ordinary (stage contra)

theorem exact_compiler_sibling_state (contra : Bool) :
    ((run contra).bind fun x => (build x).map verified).getD false = true := by
  cases contra <;> decide +kernel

theorem actual_order_and_nonvacuous_same_model (contra : Bool) :
    ∃ (x : Ordered contra) (p : Pair x), run contra = some x ∧ build x = some p ∧
      Classify (Local p) rootQuery (.selected (.node 97 [.node 98 [],.node 100 []])) ∧
      (∀ u,Fits p.b.world (model contra u) (interpreted p.b.world.board (model contra u))) ∧
      ∀ (m : Assignment) (v : NativeViews), Fits p.b.world m v →
        Evidence (Meaning p m v) rootQuery (.node 97 [.node 98 [],.node 100 []]) := by
  have closed := exact_compiler_sibling_state contra
  cases ran : run contra with
  | none => rw [ran] at closed; cases closed
  | some x =>
    rw [ran] at closed
    change ((build x).map verified).getD false = true at closed
    cases built : build x with
    | none => rw [built] at closed; cases closed
    | some p =>
      rw [built] at closed
      have confirmed := Bool.and_eq_true_iff.mp (show verified p = true from closed)
      have ids := of_decide_eq_true (Bool.and_eq_true_iff.mp confirmed.1).1
      refine ⟨x,p,rfl,built,?_,?_,?_⟩
      · have root := actual_ordered_sibling_dict p
        rw [ids.1,ids.2.1,ids.2.2.1] at root
        exact root
      · intro u
        exact ⟨(exact_model_iff confirmed.2 _).mpr (model_fits_both_scopes contra u), fun _ => rfl⟩
      · intro m v fit
        have root := actual_sibling_dict_same_model p ran m v fit
        rw [ids.1,ids.2.1,ids.2.2.1] at root
        exact root

end Yulang.GeneralDeclarativeWitnessTwoChildModel363
