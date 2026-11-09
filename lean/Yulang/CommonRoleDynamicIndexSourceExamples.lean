import Yulang.CommonRoleDynamicIndexSourceExecution

/-! Source names 10, 20 and 30, with two occurrences of 10. -/
namespace Yulang.CommonRoleDynamicIndexSourceExamples
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
open CommonRoleDynamicIndexSourceExecution (initial)
open CommonRoleDynamicIndexSource (saturate)

abbrev table : List Nat := [10,10,20,30]
def requests : CommonRoleDynamicIndexSource.Requests := [(10,20),(20,30)]
def seed : State table.length := extend State.empty 0 .str

theorem well_scoped : CommonRoleDynamicIndexSource.WellScoped table requests := by
  intro r hr
  simp [requests] at hr
  rcases hr with rfl | rfl
  · exact ⟨0,2,rfl,rfl⟩
  · exact ⟨2,3,rfl,rfl⟩

theorem alias_and_downstream_present :
    (1 : Fin table.length) ∈ saturate table (initial table seed) requests ∧
    (2 : Fin table.length) ∈ saturate table (initial table seed) requests ∧
    (3 : Fin table.length) ∈ saturate table (initial table seed) requests := by decide

theorem downstream_initially_pending :
    CommonRoleOrdinaryKnownness.produceIndex (initial table seed) 2 3 = none := by decide

def aliasRecorded : State table.length := extend (initial table seed) 1 .str

/-- Both actual calls use the ordinary producer; the second receiver only gets
its evidence from the first call's output equation. -/
theorem actual_named_steps :
    CommonRoleOrdinaryKnownness.produceIndex aliasRecorded 1 2 =
      some (extend aliasRecorded 2 .str) ∧
    CommonRoleOrdinaryKnownness.produceIndex (extend aliasRecorded 2 .str) 2 3 =
      some (extend (extend aliasRecorded 2 .str) 3 .str) := by
  constructor <;> apply CommonRoleOrdinaryKnownness.index_from_detected_str <;> decide

end Yulang.CommonRoleDynamicIndexSourceExamples
