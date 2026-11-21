import Yulang.GeneralDeclarativeRepeatResolve327
import Yulang.CommonNominalFullModelMap
import Yulang.CommonBoundCoalescing

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralDeclarativeRepeatModels327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatGraph327
open GeneralDeclarativeRepeatResolve327
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal subtype_refl common_pair_iff
  common_union_is_join common_inter_is_meet)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeEvidence320 (Evidence)

def value (flag : Bool) : Ty := if flag then .base .bool else .base .int
abbrev title (flag : Bool) := nominal 0 [.inl (value flag)]

def assignment (flag : Bool) : Assignment := fun n =>
  ((if n = 0 then CommonNominalFullCarrier.pair .bottom .bottom
    else if n = 1 then CommonNominalFullCarrier.pair (value flag) (value flag)
    else if n = 2 then CommonNominalFullCarrier.pair .top .top
    else if n = 3 ∨ n = 9 ∨ n = 12 ∨ n = 15 then .bottom
    else if n = 4 ∨ n = 10 ∨ n = 14 ∨ n = 17 then .top
    else if n = 11 then CommonNominalFullCarrier.pair (CommonNominalFullCarrier.pair (value flag) (value flag)) .bottom
    else if n = 18 then .union .bottom .bottom
    else if n = 19 then .inter .top .top
    else if n = 5 ∨ n = 6 ∨ n = 20 ∨ n = 21 ∨ n = 22 then title flag
    else value flag),Common.rowEmpty)

theorem bottom_le (type : Ty) : Subtype .bottom type := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs _
  exact CommonNominalFullDemand.probeAt_bottom rank obs

theorem actual_top (flag : Bool) : Subtype (value flag) .top := by
  cases flag
  · exact GeneralDeclarativeRepeat320.int_top
  · exact (CommonNominalFullModelMap.subtype_exact _ _).mpr (CommonBoundCoalescing.le_top (.base .bool))

theorem actual_not_bottom (flag : Bool) : ¬Subtype (value flag) .bottom := by
  intro h
  have seen := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.role 0) (by trivial)
  cases flag <;>
    simp [value,CommonNominalFullCarrier.observeTy,CommonNominalFullDemand.ProbeAt,
      CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep,
      CommonNominalSyntax.Layer.evalAt] at seen

theorem top_not_actual (flag : Bool) : ¬Subtype .top (value flag) := by
  cases flag
  · exact GeneralDeclarativeRepeat320.top_not_int
  · intro h
    let e : CommonNominalFullDemand.Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .bool]⟩
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 0) 0 e (.role 0) List.mem_cons_self

theorem inhabited (flag : Bool) : Models result (assignment flag) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a present
    change a ∈ [PresenceNormalForm.Atom.tyLe (.var 13) (.var 13),.tyLe (.var 13) (.var 13),
      .tyLe (.var 16) (.var 13),.tyLe (.var 13) (.var 16),
      .tyLe (.var 18) (.union (.var 12) (.var 15)),.tyLe (.union (.var 12) (.var 15)) (.var 18),
      .tyLe (.var 19) (.inter (.var 14) (.var 17)),.tyLe (.inter (.var 14) (.var 17)) (.var 19),
      .tyLe (.var 18) (.var 13),.tyLe (.var 13) (.var 19)] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact subtype_refl _
      | exact (common_union_is_join ..).mpr ⟨bottom_le _,bottom_le _⟩
      | exact (common_inter_is_meet ..).mpr ⟨actual_top _,actual_top _⟩
  · intro link present
    rw [checked_intervals] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact subtype_refl _
      | exact (common_pair_iff ..).mpr ⟨bottom_le _,bottom_le _⟩
      | exact (common_pair_iff ..).mpr ⟨actual_top _,actual_top _⟩
      | exact bottom_le _
      | exact actual_top _
  · intro row present
    rw [exact_rows] at present
    simp only [presentRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact eqv_refl _

theorem center_is_not_an_endpoint (flag : Bool) :
    ¬Equivalent ((assignment flag) 1).1 ((assignment flag) 0).1 ∧
    ¬Equivalent ((assignment flag) 1).1 ((assignment flag) 2).1 := by
  constructor
  · intro h
    exact actual_not_bottom flag ((common_pair_iff (value flag) (value flag) .bottom .bottom).mp h.1).1
  · intro h
    exact top_not_actual flag ((common_pair_iff .top .top (value flag) (value flag)).mp h.2).1

theorem genuine_two_models (flag : Bool) :
    Models result (assignment flag) ∧ Evidence reg interp (assignment flag) root dict ∧
      (¬Equivalent ((assignment flag) 1).1 ((assignment flag) 0).1 ∧
       ¬Equivalent ((assignment flag) 1).1 ((assignment flag) 2).1) :=
  ⟨inhabited flag,every_model _ (inhabited flag),center_is_not_an_endpoint flag⟩

theorem no_center_row : ¬∃ rhs, (⟨1,rhs⟩ : Equation) ∈ result.equations := by
  rintro ⟨rhs,h⟩
  rw [exact_rows] at h
  simp only [presentRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> have no := congrArg Equation.left h <;> cases no

end Yulang.GeneralDeclarativeRepeatModels327
