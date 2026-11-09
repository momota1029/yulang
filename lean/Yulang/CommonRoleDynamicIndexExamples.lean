import Yulang.CommonRoleDynamicIndexClosure

/-! Regression for the general finite dynamic Index closure. The downstream
receiver is initially unknown; the first real associated equation enables it. -/
namespace Yulang.CommonRoleDynamicIndexExamples
open CommonRoleDynamicIndexClosure
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)

def chain : Edges 3 := [(0,1),(1,2)]
def initial : State 3 := extend State.empty 0 .str

theorem downstream_initially_pending :
    CommonRoleOrdinaryKnownness.produceIndex initial 1 2 = none := by decide

theorem root_evidence : CommonRoleOrdinaryKnownness.Evidence initial.atoms 0 .str := by
  constructor <;> simp [initial, extend, CommonRoleCandidateStateFrontier.equality, State.empty]

theorem final_derived : Derived initial chain 2 :=
  .index (i := 1) (by simp [chain]) (.index (i := 0) (by simp [chain]) (.seed root_evidence))

theorem final_present : (2 : Fin 3) ∈ saturate initial chain :=
  (saturate_exact initial chain 2).mpr final_derived

/-- No externally supplied output scalar: both invocations execute the checked
Index declaration body using the receiver evidence of their actual input state. -/
theorem actual_two_steps :
    CommonRoleOrdinaryKnownness.produceIndex initial 0 1 =
      some (extend initial 1 .str) ∧
    CommonRoleOrdinaryKnownness.produceIndex (extend initial 1 .str) 1 2 =
      some (extend (extend initial 1 .str) 2 .str) := by
  constructor <;> apply CommonRoleOrdinaryKnownness.index_from_detected_str <;> decide

end Yulang.CommonRoleDynamicIndexExamples
