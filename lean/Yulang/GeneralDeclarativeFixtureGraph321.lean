import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeGraphRows321
import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFixtureGraph321
open GeneralDeclarativeExampleSource320 (state nApp)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def weight (name : Nat) : Nat := if name ≤ 2 ∨ name = 6 then 1 else 0

theorem bounds_weight {a b : Nat} (known : Bound state.normal a b) : weight a = weight b := by
  induction known with
  | refl => rfl
  | interval member =>
    change _ ∈ [(0,1),(1,2)] at member
    rcases List.mem_cons.mp member with equal|later
    · cases equal
      rfl
    · cases List.mem_singleton.mp later
      rfl
  | constraint member => cases member
  | trans _ _ before after => exact before.trans after

theorem alias_equation_weight {a b : Nat} (same : (⟨a,.variable b⟩ : Equation) ∈ state.equations) :
    weight a = weight b := by
  change _ ∈ ([⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,
      ⟨5,.variable 3⟩,⟨6,nApp 5⟩] : List Equation) at same
  simp only [List.mem_cons,List.not_mem_nil,or_false] at same
  rcases same with equal|equal|equal|equal|equal <;> cases equal <;> rfl

theorem aliases_weight (a b : Nat) (same : Alias state a b) : weight a = weight b := by
  induction same with
  | bounds first _ => exact bounds_weight first
  | forward h => exact alias_equation_weight h
  | backward h => exact (alias_equation_weight h).symm
  | trans _ _ before after => exact before.trans after

theorem child_weight (a : Nat) (head : Shape) (b : Nat) (seen : observed state a head)
   (child : b ∈ head.children) : weight b < weight a := by
  obtain ⟨code,member,matchShape⟩ := seen
  change _ ∈ ([⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,
      ⟨5,.variable 3⟩,⟨6,nApp 5⟩] : List Equation) at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with pair|pair|pair|pair|pair <;> cases pair
  · change some (.nominal 0 [3]) = some head at matchShape
    cases matchShape
    cases List.mem_singleton.mp child
    decide +kernel
  · change some (.nominal 0 [3]) = some head at matchShape
    cases matchShape
    cases List.mem_singleton.mp child
    decide +kernel
  · change some (.primitive (.scalar .int) []) = some head at matchShape
    cases matchShape
    cases child
  · cases matchShape
  · change some (.nominal 0 [5]) = some head at matchShape
    cases matchShape
    cases List.mem_singleton.mp child
    decide +kernel

theorem not_recursive : ∀ name, ¬AliasCycle state (observed state) name :=
  GeneralDeclarativeRank321.graph_no_cycle weight aliases_weight child_weight

end Yulang.GeneralDeclarativeFixtureGraph321
