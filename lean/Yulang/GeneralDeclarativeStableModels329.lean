import Yulang.GeneralDeclarativeStableResult329
import Yulang.GeneralDeclarativeNestedModels328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeStableModels329
open GeneralDeclarativeStableFixture329 (final spans base tied child returnRow childRow tie inputRows pairRow)
open GeneralDeclarativeStableProbe329 (table)
open GeneralDeclarativeOpaqueFixture328 (prepared oldRows)
open GeneralDeclarativeStableResult329 (every_model dict)
open GeneralDeclarativeRepeatDecl327 (reg interp root)
open GeneralDeclarativeRepeat320 (int)
open GeneralDeclarativeNestedModels328 (boolType payload int_in_payload payload_lt_top payload_gt_int)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeStableTies329 (model_batch pairOf rows)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal pair subtype_refl subtype_trans common_pair_iff common_inter_is_meet)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)

def middle (a b : Ty) : Ty := .inter (pair a b) .top
abbrev compound (a : Ty) : Ty := nominal 0 [.inl a]

def assignment (a b : Ty) : Assignment := fun n =>
  ((if n = 0 then pair int int else if n = 1 then middle a b else if n = 2 then pair .top .top
    else if n = 4 then .top else if n = 7 then a else if n = 8 then b else if n = 12 then boolType
    else if n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 11 then compound a else int),Common.rowEmpty)

theorem visible_middle (a b : Ty) : Equivalent (middle a b) (pair a b) :=
  ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
    (common_inter_is_meet ..).mpr ⟨subtype_refl _,GeneralNominalTopObservation.le_top _⟩⟩

theorem ordinary_atoms {a b : Ty} (first : Subtype int a) (last : Subtype int b) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (assignment a b) final.normal.ordinary := by
  intro atom which
  change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 3) (.var 7),.tyLe (.var 7) (.var 4),
    .tyLe (.var 3) (.var 8),.tyLe (.var 8) (.var 4)] at which
  simp only [List.mem_cons,List.not_mem_nil,or_false] at which
  rcases which with h|h|h|h <;> cases h
  · exact first
  · exact GeneralNominalTopObservation.le_top _
  · exact last
  · exact GeneralNominalTopObservation.le_top _

theorem lower_interval {a b : Ty} (first : Subtype int a) (last : Subtype int b) :
    Subtype (pair int int) (middle a b) :=
  subtype_trans ((common_pair_iff ..).mpr ⟨first,last⟩) (visible_middle a b).2
theorem upper_interval (a b : Ty) :
    Subtype (middle a b) (pair .top .top) :=
  subtype_trans (visible_middle a b).1 ((common_pair_iff ..).mpr
    ⟨GeneralNominalTopObservation.le_top _,GeneralNominalTopObservation.le_top _⟩)

theorem before {a b : Ty} (first : Subtype int a) (last : Subtype int b) : Models prepared (assignment a b) := by
  refine ⟨⟨ordinary_atoms first last,?_⟩,?_⟩
  · intro span there
    change span ∈ [(0,1),(1,2)] at there
    rcases List.mem_cons.mp there with rfl|remaining
    · exact lower_interval first last
    · cases List.mem_singleton.mp remaining
      exact upper_interval a b
  · intro row stored
    change row ∈ oldRows ++ [pairRow] at stored
    simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at stored
    rcases stored with h|h|h|h <;> cases h
    all_goals first | exact eqv_refl _ | exact visible_middle _ _

theorem after {a b : Ty} (first : Subtype int a) (last : Subtype int b) (same : Equivalent a b) :
    Models final (assignment a b) := by
  refine ⟨⟨ordinary_atoms first last,?_⟩,?_⟩
  · intro span there
    change span ∈ [(0,1),(1,2),(9,10),(10,11)] at there
    simp only [List.mem_cons,List.not_mem_nil,or_false] at there
    rcases there with h|h|h|h <;> cases h
    · exact lower_interval first last
    · exact upper_interval a b
    · exact subtype_refl _
    · exact subtype_refl _
  · intro row stored
    rw [table] at stored
    simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at stored
    rcases stored with h|h|h|h|h|h|h|h|h|h <;> cases h
    all_goals first | exact eqv_refl _ | exact visible_middle _ _ | exact same

theorem eliminated {a b : Ty} (mismatch : ¬Equivalent a b) : ¬Models tied (assignment a b) := by
  intro models
  have fromWrite := ((model_batch (s := prepared) base (spans.map pairOf) (assignment a b)).mp models).2
  have chosen : (0,8) ∈ spans.map pairOf := List.mem_cons_of_mem _ List.mem_cons_self
  exact mismatch (eqv_symm (fromWrite (0,8) chosen))

theorem current_exact (a b : Ty) :
    Models final (assignment a b) ↔ Subtype int a ∧ Subtype int b ∧ Equivalent a b := by
  constructor
  · intro h
    refine ⟨h.1.1 _ List.mem_cons_self,h.1.1 _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),?_⟩
    exact h.2 _ (GeneralDeclarativeStableFixture329.ordinary_rows
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  · rintro ⟨x,y,same⟩
    exact after x y same

theorem genuine :
    (Models prepared (assignment int payload) ∧ ¬Models tied (assignment int payload)) ∧
    Models final (assignment payload payload) ∧
    Evidence reg interp (assignment payload payload) root dict ∧
    ¬Equivalent ((assignment payload payload) 1).1 ((assignment payload payload) 0).1 ∧
    ¬Equivalent ((assignment payload payload) 1).1 ((assignment payload payload) 2).1 := by
  have yes := after int_in_payload int_in_payload (eqv_refl _)
  refine ⟨⟨before (subtype_refl _) int_in_payload,eliminated (fun h => payload_gt_int h.2)⟩,
    yes,every_model _ yes,?_,?_⟩
  · intro point
    exact payload_gt_int ((common_pair_iff ..).mp (subtype_trans (visible_middle ..).2 point.1)).1
  · intro point
    exact payload_lt_top ((common_pair_iff ..).mp (subtype_trans point.2 (visible_middle ..).1)).1

end Yulang.GeneralDeclarativeStableModels329
