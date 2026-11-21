import Yulang.GeneralDeclarativeOpaqueFixtureResolve328
import Yulang.GeneralNominalTopObservation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeOpaqueFixtureModels328
open GeneralDeclarativeOpaqueFixture328
open GeneralDeclarativeOpaqueFixtureResolve328
open GeneralDeclarativePairDecl326 (root reg interpret)
open GeneralDeclarativeOpaqueChannel328 (project)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeRepeat320 (int int_top top_not_int)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm eqv_refl)
open CommonNominalFullCarrier (Ty pair Equivalent Subtype subtype_refl subtype_trans common_inter_is_meet common_pair_iff)

abbrev a (swap : Bool) : Ty := if swap then int else .top
abbrev b (swap : Bool) : Ty := if swap then .top else int
abbrev hidden (swap : Bool) : Ty := .inter (pair (a swap) (b swap)) .top

def assignment (swap : Bool) : Assignment := fun n =>
  ((if n = 0 then pair int int else if n = 1 then hidden swap else if n = 2 then pair .top .top
    else if n = 4 then .top else if n = 5 ∨ n = 6 ∨ n = 7 then a swap else if n = 8 then b swap else int),Common.rowEmpty)

theorem hidden_equiv (swap : Bool) : Equivalent (hidden swap) (pair (a swap) (b swap)) := by
  refine ⟨?_,(common_inter_is_meet ..).mpr ⟨subtype_refl _,GeneralNominalTopObservation.le_top _⟩⟩
  exact ((common_inter_is_meet ..).mp (subtype_refl (hidden swap))).1

theorem actual_reads (swap : Bool) :
    project false (hidden swap) = some (a swap) ∧ project true (hidden swap) = some (b swap) :=
  ⟨rfl,rfl⟩

theorem fitted (swap : Bool) : Models final (assignment swap) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro atom seen
    change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 3) (.var 7),.tyLe (.var 7) (.var 4),
      .tyLe (.var 3) (.var 8),.tyLe (.var 8) (.var 4)] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    cases swap <;> rcases seen with rfl|rfl|rfl|rfl
    all_goals first | exact subtype_refl _ | exact int_top
  · intro interval listed
    change _ ∈ [(0,1),(1,2)] at listed
    rcases List.mem_cons.mp listed with rfl|other
    · have admitted := (common_pair_iff int int (a swap) (b swap)).mpr (by
        cases swap
        · exact ⟨int_top,subtype_refl _⟩
        · exact ⟨subtype_refl _,int_top⟩)
      exact subtype_trans admitted (hidden_equiv swap).2
    · cases List.mem_singleton.mp other
      have admitted := (common_pair_iff (a swap) (b swap) .top .top).mpr (by
        cases swap
        · exact ⟨subtype_refl _,int_top⟩
        · exact ⟨int_top,subtype_refl _⟩)
      exact subtype_trans (hidden_equiv swap).1 admitted
  · intro row found
    rw [GeneralDeclarativeOpaqueFixtureProbe328.exact_rows] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact eqv_refl _ | exact hidden_equiv swap

theorem center_not_endpoint (swap : Bool) :
    ¬Equivalent ((assignment swap) 1).1 ((assignment swap) 0).1 ∧
    ¬Equivalent ((assignment swap) 1).1 ((assignment swap) 2).1 := by
  constructor
  · intro equal
    have lowered := (common_pair_iff (a swap) (b swap) int int).mp
      (subtype_trans (hidden_equiv swap).2 equal.1)
    cases swap
    · exact top_not_int lowered.1
    · exact top_not_int lowered.2
  · intro equal
    have wider := (common_pair_iff .top .top (a swap) (b swap)).mp
      (subtype_trans equal.2 (hidden_equiv swap).1)
    cases swap
    · exact top_not_int wider.2
    · exact top_not_int wider.1

theorem exact_opaque_fixture (swap : Bool) :
    (¬ ∃ rhs, (⟨1,rhs⟩ : Equation) ∈ initial.equations) ∧
    Models final (assignment swap) ∧ Evidence reg interpret (assignment swap) root dict ∧
      (¬Equivalent ((assignment swap) 1).1 ((assignment swap) 0).1 ∧
       ¬Equivalent ((assignment swap) 1).1 ((assignment swap) 2).1) :=
  ⟨no_old_center,fitted swap,certified _ (fitted swap),center_not_endpoint swap⟩

end Yulang.GeneralDeclarativeOpaqueFixtureModels328
