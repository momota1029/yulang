import Yulang.GeneralGeneratedDisplayObserved299
import Yulang.GeneralGeneratedRigidCompile299

namespace Yulang.GeneralGeneratedDictionaryControls299
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryRankCheck299
open GeneralGeneratedDictionaryFiniteCap299
open GeneralGeneratedDictionaryMemo299
open GeneralGeneratedDictionaryMemoCheck299
open GeneralGeneratedDictionaryHeight299
open GeneralGeneratedFrontierReceipt299
open CommonRoleOutermostResolver (Frontier Dictionary)

def cyclic : Read
  | 0 => some ⟨8,[0]⟩
  | _ => none

def missing : Read
  | 0 => some ⟨8,[1]⟩
  | _ => none

def repeated : Read
  | 0 => some ⟨8,[1,1]⟩
  | 1 => some ⟨9,[]⟩
  | _ => none

theorem cycle_not_accessible : ¬ Acc (Edge cyclic) 0 :=
  fun h => (acc_no_loop h) ⟨⟨8,[0]⟩,rfl,List.mem_singleton_self _⟩

theorem cycle_no_budget (cap : Nat) : run cyclic cap 0 = none := by
  cases h : run cyclic cap 0 with
  | none => rfl
  | some d => exact False.elim (cycle_not_accessible (success_accessible cyclic cap 0 d h))

theorem cycle_check_false : checkMemo cyclic [0] 1 = false := rfl

theorem missing_not_closed : ¬ Closed missing := by
  intro closed
  obtain ⟨row,hit⟩ := closed 0 ⟨8,[1]⟩ rfl 1 (List.mem_singleton_self _)
  cases hit

theorem missing_result : run missing 5 0 = none := rfl

theorem missing_check_false : checkMemo missing [0,1] 2 = false := rfl

theorem retains_duplicate : run repeated 2 0 = some (.node 8 [.node 9 [],.node 9 []]) := rfl

theorem ordered_height : height (.node 8 [.node 9 [],.node 9 []]) = 2 := by
  simp [height,tall]

theorem exactly_two_or_more (n : Nat) :
    run repeated n 0 = some (.node 8 [.node 9 [],.node 9 []]) ↔ 2 ≤ n := by
  rw [height_threshold _ 2 _ _ retains_duplicate,ordered_height]

theorem no_false_rejection :
    compile GeneralGeneratedDisplayObserved299.lookup (fun _ => none) 0 = .unindexed ∧
      compile GeneralGeneratedDisplayObserved299.lookup (fun _ => none) 9 = .absent := by
  exact ⟨rfl,rfl⟩

theorem diagnostic_distinction :
    compile (fun (_ : Nat) => (some (.pending : Frontier Unit))) (fun _ => none) 0 = .pending ∧
      compile (fun _ => (some (.rejected : Frontier Unit))) (fun _ => none) 0 = .rejected ∧
      compile (fun _ => (some (.ambiguous : Frontier Unit))) (fun _ => none) 0 = .ambiguous :=
  ⟨rfl,rfl,rfl⟩

theorem rigid_depth_check :
    checkMemo GeneralGeneratedRigidNested299.table [0,1,2] 2 = false ∧
      checkMemo GeneralGeneratedRigidNested299.table [0,1,2] 3 = true ∧
      bitFirst GeneralGeneratedRigidNested299.table [0,1,2] 0 3 = some 3 :=
  ⟨rfl,rfl,rfl⟩

end Yulang.GeneralGeneratedDictionaryControls299
