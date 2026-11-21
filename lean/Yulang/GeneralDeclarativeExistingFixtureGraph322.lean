import Yulang.GeneralDeclarativeExistingFixture322
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingFixtureGraph322
open GeneralDeclarativeExistingFixture322 (state equations product nominalCode)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (Equation)

def weight (name : Nat) : Nat :=
  if name ≤ 2 ∨ name = 6 ∨ name = 14 then 2 else if name = 16 ∨ name = 17 then 0 else 1

theorem bound_weight {a b : Nat} (known : Bound state.normal a b) : weight a = weight b := by
  induction known with
  | refl => rfl
  | interval used =>
    change _ ∈ [(0,1),(1,2),(8,9),(9,10)] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with equal|equal|equal|equal <;> cases equal <;> rfl
  | constraint used => cases used
  | trans _ _ ab bc => exact ab.trans bc

theorem alias_row_weight {a b : Nat} (known : (⟨a,.variable b⟩ : Equation) ∈ state.equations) :
    weight a = weight b := by
  change _ ∈ equations at known
  simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at known
  rcases known with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem alias_weight (a b : Nat) (known : Alias state a b) : weight a = weight b := by
  induction known with
  | bounds ab _ => exact bound_weight ab
  | forward row => exact alias_row_weight row
  | backward row => exact (alias_row_weight row).symm
  | trans _ _ ab bc => exact ab.trans bc

theorem shape_weight (a : Nat) (head : Shape) (b : Nat) (known : observed state a head)
    (edge : b ∈ head.children) : weight b < weight a := by
  obtain ⟨code,member,seen⟩ := known
  change _ ∈ equations at member
  simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h
  all_goals cases seen
  all_goals first
  | (have same : b = _ := List.mem_singleton.mp edge; subst b; decide +kernel)
  | (change b ∈ [16,17] at edge
     simp only [List.mem_cons,List.not_mem_nil,or_false] at edge
     rcases edge with rfl|rfl <;> decide +kernel)

theorem no_cycle : ∀ name, ¬AliasCycle state (observed state) name :=
  GeneralDeclarativeRank321.graph_no_cycle weight alias_weight shape_weight

end Yulang.GeneralDeclarativeExistingFixtureGraph322
