import Yulang.GeneralDeclarativeWitnessNominalDictionary364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 89000
set_option maxHeartbeats 124000000
namespace Yulang.GeneralDeclarativeWitnessNominalDictionaryModel364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessActualNominalLeaf364 (FinishedRun demo actual)
open GeneralDeclarativeWitnessNominalDictionary364 (Local Meaning nominal_tree_selected same_model_selected_nominal_dictionary)
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

def prefixState (contra : Bool) : State :=
  let prior := GeneralDeclarativeWitnessSeparateAuthorModel362.state contra
  ⟨⟨prior.normal.ordinary ++ GeneralDeclarativeWitnessCrossOwnerModel362.rows.take 16,prior.normal.intervals⟩,prior.equations⟩

def rows : List (Atom Nat) :=
  [(61,61),(61,61),(314,60),(60,314),(315,62),(62,315),(314,61),(61,315)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def stage (contra : Bool) : State :=
  let old := prefixState contra
  ⟨⟨old.normal.ordinary ++ rows,old.normal.intervals⟩,old.equations⟩

def model (contra u : Bool) : Assignment := fun n =>
  let old := GeneralDeclarativeWitnessCrossOwnerModel362.model contra u
  if n = 314 then old 60 else if n = 315 then old 62 else old n

theorem model_fits_actual_payload_copies (contra u : Bool) : Models (stage contra) (model contra u) := by
  let old := GeneralDeclarativeWitnessCrossOwnerModel362.model contra u
  let prior := prefixState contra
  have fresh : (stateNames prior).all (fun n => decide (n ≠ 314 ∧ n ≠ 315)) = true := by
    cases contra <;> decide +kernel
  have same (n : Nat) (active : n ∈ stateNames prior) : old n = model contra u n := by
    obtain ⟨a,b⟩ := of_decide_eq_true (List.all_eq_true.mp fresh n active)
    simp [model,old,a,b]
  have all := GeneralDeclarativeWitnessCrossOwnerModel362.fits_current contra u
  have pre : Models prior old := by
    refine ⟨⟨?_,all.1.2⟩,all.2⟩
    intro row seen
    apply all.1.1
    rcases (List.mem_append.mp seen : row ∈ (GeneralDeclarativeWitnessSeparateAuthorModel362.state contra).normal.ordinary ∨
      row ∈ GeneralDeclarativeWitnessCrossOwnerModel362.rows.take 16) with earlier|extra
    · exact List.mem_append_left _ earlier
    · exact List.mem_append_right _ (List.mem_of_mem_take extra)
  have retained := (preserves_models prior same).mp pre
  refine ⟨⟨?_,retained.1.2⟩,retained.2⟩
  intro a stored
  rcases (List.mem_append.mp stored : a ∈ prior.normal.ordinary ∨ a ∈ rows) with before|after
  · exact retained.1.1 _ before
  · simp only [rows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at after
    rcases after with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases u <;> first | exact subtype_refl _ | exact endpoints_ordered

def verified {contra x} (z : @FinishedRun contra x) : Bool :=
  actual z && exact z.leaf.world.ordinary (stage contra)

theorem actual_normal_state_has_scoped_payload_copies (contra : Bool) :
    ((run contra).bind fun x => (demo x).map verified).getD false = true := by
  cases contra <;> decide +kernel

theorem actual_elected_nominal_dictionary_in_all_fits (contra : Bool) :
    ∃ (x : Ordered contra) (z : FinishedRun x), run contra = some x ∧ demo x = some z ∧
      Classify (Local z) rootQuery (.selected (.node 97 [.node 99 []])) ∧
      (∀ u,Fits z.leaf.world (model contra u) (interpreted z.leaf.world.board (model contra u))) ∧
      ∀ (m : Assignment) (v : NativeViews), Fits z.leaf.world m v →
        Evidence (Meaning z m v) rootQuery (.node 97 [.node 99 []]) := by
  have closed := actual_normal_state_has_scoped_payload_copies contra
  cases ran : run contra with
  | none => rw [ran] at closed; cases closed
  | some x =>
    rw [ran] at closed
    change ((demo x).map verified).getD false = true at closed
    cases built : demo x with
    | none => rw [built] at closed; cases closed
    | some z =>
      rw [built] at closed
      have confirmed := Bool.and_eq_true_iff.mp (show verified z = true from closed)
      have ids := of_decide_eq_true confirmed.1
      refine ⟨x,z,rfl,built,?_,?_,?_⟩
      · have root := nominal_tree_selected z
        rw [ids.1,ids.2.1] at root
        exact root
      · intro u
        exact ⟨(exact_model_iff confirmed.2 _).mpr (model_fits_actual_payload_copies contra u), fun _ => rfl⟩
      · intro m v fit
        have root := same_model_selected_nominal_dictionary z ran m v fit
        rw [ids.1,ids.2.1] at root
        exact root

end Yulang.GeneralDeclarativeWitnessNominalDictionaryModel364
