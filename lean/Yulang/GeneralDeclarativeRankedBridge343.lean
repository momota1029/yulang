import Yulang.GeneralDeclarativeModeBridge343
import Yulang.GeneralDeclarativeTaggedElection340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15200
set_option maxHeartbeats 5400000
namespace Yulang.GeneralDeclarativeRankedBridge343
open GeneralDeclarativeModeBridge343 (joined rows pair)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

def CoLevels (rank : Nat → Nat) (x y : Capture) : Prop :=
  rank x.lower = rank y.lower ∧ rank x.center = rank y.center ∧ rank x.upper = rank y.upper

theorem directed {rank : Nat → Nat} {x y : Capture} (known : CoLevels rank x y)
    (row : Equation) (there : row ∈ pair x y) :
    ∃ n, row.right = .variable n ∧ rank row.left = rank n := by
  rcases List.mem_cons.mp there with one|later
  · cases one
    exact ⟨_,rfl,known.1⟩
  · rcases List.mem_cons.mp later with one|last
    · cases one
      exact ⟨_,rfl,known.2.1⟩
    · cases List.mem_singleton.mp last
      exact ⟨_,rfl,known.2.2⟩

theorem whole {rank : Nat → Nat} {xs ys : List Capture} (observed : All₂ (CoLevels rank) xs ys) :
    ∀ row ∈ rows xs ys, ∃ n, row.right = .variable n ∧ rank row.left = rank n := by
  induction observed with
  | nil => intro _ none; cases none
  | cons hd _ ih =>
    intro row written
    rcases List.mem_append.mp written with earlier|later
    · exact directed hd row earlier
    · exact ih row later

/-- Adding the explicit mode aliases leaves this K2 certificate valid
when the matched names independently have the same rank in every
mode. Semantic equivalence alone is not claimed to imply this test. -/
theorem preserves_rank {s : State} {x y : Demand} {rank : Nat → Nat}
    (older : Ranked s rank) (pairs : All₂ (CoLevels rank) x.arguments y.arguments) :
    Ranked (joined s x y) rank := by
  constructor
  · exact older.bounded
  · intro a b h
    rcases List.mem_append.mp h with old|latest
    · exact older.flat old
    · obtain ⟨there,printed,ranked⟩ := whole pairs ⟨a,.variable b⟩ latest
      cases printed
      exact ranked
  · intro row here name used nonVar
    rcases List.mem_append.mp here with old|latest
    · exact older.compound row old name used nonVar
    · obtain ⟨_,printed,_⟩ := whole pairs row latest
      exact False.elim (nonVar _ printed)

end Yulang.GeneralDeclarativeRankedBridge343
