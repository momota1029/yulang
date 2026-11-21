import Yulang.GeneralDeclarativeNestedResolve328
import Yulang.GeneralNominalTopObservation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeNestedModels328
open GeneralDeclarativeNestedDecl328 (root reg interpret)
open GeneralDeclarativeNestedState328
open GeneralDeclarativeNestedResolve328
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeRepeat320 (int)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype Equivalent pair variant nominal subtype_refl subtype_trans
  common_pair_iff common_variant_iff common_inter_is_meet common_union_is_join observeTy)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullDemand (Environment ProbeAt ProbeStep MaskedProbeStep)

abbrev boolType : Ty := .base .bool
abbrev payload : Ty := .union int boolType
abbrev fixed : Ty := nominal 0 [.inl boolType]
abbrev lowerType : Ty := pair (variant 4 int) fixed
abbrev middleType : Ty := pair (variant 4 payload) fixed
abbrev upperType : Ty := pair (variant 4 .top) fixed
abbrev hidden : Ty := .inter middleType .top

def model : Assignment := fun n =>
  ((if n = 0 then lowerType else if n = 1 then hidden else if n = 2 then upperType
    else if n = 4 then .top else if n = 5 ∨ n = 6 ∨ n = 17 then payload
    else if n = 9 ∨ n = 10 then boolType else if n = 11 then variant 4 int
    else if n = 13 then variant 4 .top else if n = 15 then variant 4 payload
    else if n = 12 ∨ n = 14 ∨ n = 16 then fixed else int),Common.rowEmpty)

theorem int_in_payload : Subtype int payload :=
  ((common_union_is_join ..).mp (subtype_refl payload)).1

theorem payload_lt_top : ¬Subtype .top payload := by
  intro bad
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int,.base .bool]⟩
  have violates := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (bad 0) 0 env (.role 0)
  exact violates ⟨List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem payload_gt_int : ¬Subtype payload int := by
  intro bad
  have wrong := ((common_union_is_join ..).mp bad).2
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int]⟩
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (wrong 0) 0 env (.role 0)
    List.mem_cons_self
  simp [env,ProbeAt,ProbeStep,MaskedProbeStep,observeTy,CommonNominalSyntax.Layer.evalAt] at impossible

theorem hidden_actual : Equivalent hidden middleType :=
  ⟨((common_inter_is_meet ..).mp (subtype_refl hidden)).1,
    (common_inter_is_meet ..).mpr ⟨subtype_refl _,GeneralNominalTopObservation.le_top _⟩⟩

theorem lo_to_mid : Subtype lowerType middleType :=
  (common_pair_iff ..).mpr ⟨(common_variant_iff ..).mpr int_in_payload,subtype_refl _⟩
theorem mid_to_hi : Subtype middleType upperType :=
  (common_pair_iff ..).mpr ⟨(common_variant_iff ..).mpr (GeneralNominalTopObservation.le_top _),subtype_refl _⟩

theorem inhabited : Models final model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro atom present
    change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 11) (.var 15),.tyLe (.var 15) (.var 13),
        .tyLe (.var 12) (.var 16),.tyLe (.var 16) (.var 14),.tyLe (.var 3) (.var 17),
        .tyLe (.var 17) (.var 4)] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h|h|h|h <;> cases h
    · exact (common_variant_iff ..).mpr int_in_payload
    · exact (common_variant_iff ..).mpr (GeneralNominalTopObservation.le_top _)
    · exact subtype_refl _
    · exact subtype_refl _
    · exact int_in_payload
    · exact GeneralNominalTopObservation.le_top _
  · intro line belongs
    change _ ∈ [(0,1),(1,2)] at belongs
    rcases List.mem_cons.mp belongs with rfl|rest
    · exact subtype_trans lo_to_mid hidden_actual.2
    · cases List.mem_singleton.mp rest
      exact subtype_trans hidden_actual.1 mid_to_hi
  · intro row found
    rw [GeneralDeclarativeNestedProbe328.exact_rows] at found
    simp only [sourceRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with x|x|x|x|x|x|x|x|x|x|x|x <;> cases x
    all_goals first | exact eqv_refl _ | exact hidden_actual

theorem distinct_from_endpoints :
    ¬Equivalent (model 1).1 (model 0).1 ∧ ¬Equivalent (model 1).1 (model 2).1 := by
  constructor
  · intro proof
    exact payload_gt_int ((common_variant_iff ..).mp
      ((common_pair_iff ..).mp (subtype_trans hidden_actual.2 proof.1)).1)
  · intro proof
    exact payload_lt_top ((common_variant_iff ..).mp
      ((common_pair_iff ..).mp (subtype_trans proof.2 hidden_actual.1)).1)

theorem genuine_nested :
    (¬∃ code, (⟨1,code⟩ : Equation) ∈ initial.equations) ∧ Models final model ∧
      Evidence reg interpret model root dict ∧
      (¬Equivalent (model 1).1 (model 0).1 ∧ ¬Equivalent (model 1).1 (model 2).1) :=
  ⟨center_absent,inhabited,certified model inhabited,distinct_from_endpoints⟩

end Yulang.GeneralDeclarativeNestedModels328
