import Yulang.GeneralDeclarativeFrameRank343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16500
set_option maxHeartbeats 6600000
namespace Yulang.GeneralDeclarativeFrameGuard343
open GeneralDeclarativeFrameShape343 (b0 b1 e0 e1 e2 edges exact_rows)
open GeneralDeclarativeFrameRank343 (level bound_levels logical_levels level_root level2_here levelL0 levelH0 level_lo level_mid level_hi)
open GeneralDeclarativePlacement343 (actual symbolic bridge view)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeTraceNames321 (names)

theorem flat {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ view.equations) : level a = level b := by
  rw [exact_rows] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with same | same | same | same | same | same | same | same <;> cases same
  · exact level_lo.trans logical_levels.1.symm
  · exact level_mid.trans logical_levels.2.1.symm
  · exact level_hi.trans logical_levels.2.2.symm

theorem compound (row : Equation) (there : row ∈ view.equations) (n : Nat) (used : n ∈ names row.right)
    (notVar : ∀ b, row.right ≠ .variable b) : level n < level row.left := by
  rw [exact_rows] at there
  simp only [List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have k : n ∈ [2,2] := used
    have eq : n = 2 := (List.mem_cons.mp k).elim id List.mem_singleton.mp
    subst n
    change level 2 < level 0
    rw [level2_here,level_root]
    decide
  · have eq : n = b0.lower := List.mem_singleton.mp used
    subst n
    change level b0.lower < level symbolic.lower
    rw [levelL0,logical_levels.1]
    decide
  · have eq : n = 2 := List.mem_singleton.mp used
    subst n
    change level 2 < level symbolic.center
    rw [level2_here,logical_levels.2.1]
    decide
  · have eq : n = b0.upper := List.mem_singleton.mp used
    subst n
    change level b0.upper < level symbolic.upper
    rw [levelH0,logical_levels.2.2]
    decide
  · change n ∈ [] at used
    cases used
  · exact False.elim (notVar _ rfl)
  · exact False.elim (notVar _ rfl)
  · exact False.elim (notVar _ rfl)

theorem ranked : Ranked view level := ⟨bound_levels,flat,compound⟩

end Yulang.GeneralDeclarativeFrameGuard343
