import Yulang.GeneralDeclarativeRelationalCheck327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFiniteCheck327
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Frontier Tree All₂ Resolves Classify Summarizes)

/-- An already supplied finite candidate derivation names the exact
ordered where demands it used. The verifier never searches for another
tree, produces a resolve result, or decides termination. -/
inductive Annotated where
  | pending
  | ambiguous
  | rejected
  | selected (key : Nat) (calls : List Demand) (nodes : List Annotated)

abbrev Rule := Demand → Frontier Demand → Prop
abbrev Checker := Demand → Frontier Demand → Bool

inductive Justifies (rules : Rule) : Demand → Annotated → Prop where
  | pending : rules d .pending → Justifies rules d .pending
  | ambiguous : rules d .ambiguous → Justifies rules d .ambiguous
  | rejected : rules d .rejected → Justifies rules d .rejected
  | selected : rules d (.selected key calls) → All₂ (Justifies rules) calls nodes →
      Justifies rules d (.selected key calls nodes)

mutual
def erase : Annotated → Tree
  | .pending => .pending
  | .ambiguous => .ambiguous
  | .rejected => .rejected
  | .selected key _ children => .selected key (eraseMany children)
termination_by t => sizeOf t

def eraseMany : List Annotated → List Tree
  | [] => []
  | first :: rest => erase first :: eraseMany rest
termination_by ts => sizeOf ts
end

mutual
def validate (localCheck : Checker) (d : Demand) : Annotated → Bool
  | .pending => localCheck d .pending
  | .rejected => localCheck d .rejected
  | .ambiguous => localCheck d .ambiguous
  | .selected key calls children =>
    localCheck d (.selected key calls) && validateMany localCheck calls children
termination_by t => sizeOf t

def validateMany (localCheck : Checker) : List Demand → List Annotated → Bool
  | [], [] => true
  | first :: later, head :: rest => validate localCheck first head && validateMany localCheck later rest
  | _, _ => false
termination_by _ ts => sizeOf ts
end

mutual
theorem validates (exactHere : ∀ d f, localCheck d f = true ↔ rules d f)
    (d : Demand) (annotated : Annotated) :
    validate localCheck d annotated = true ↔ Justifies rules d annotated := by
  cases annotated with
  | pending =>
    rw [validate]
    exact ⟨fun shown => .pending ((exactHere ..).mp shown),fun prior => by
      cases prior with | pending row => exact (exactHere ..).mpr row⟩
  | ambiguous =>
    rw [validate]
    exact ⟨fun shown => .ambiguous ((exactHere ..).mp shown),fun prior => by
      cases prior with | ambiguous row => exact (exactHere ..).mpr row⟩
  | rejected =>
    rw [validate]
    exact ⟨fun shown => .rejected ((exactHere ..).mp shown),fun prior => by
      cases prior with | rejected row => exact (exactHere ..).mpr row⟩
  | selected key cs ns =>
    rw [validate,Bool.and_eq_true,exactHere,validates_many exactHere cs ns]
    exact ⟨fun ⟨found,many⟩ => .selected found many,fun proof => by
      cases proof with | selected found many => exact ⟨found,many⟩⟩
termination_by sizeOf annotated

theorem validates_many (exactHere : ∀ d f, localCheck d f = true ↔ rules d f)
    (demands : List Demand) (annotated : List Annotated) :
    validateMany localCheck demands annotated = true ↔ All₂ (Justifies rules) demands annotated := by
  cases demands with
  | nil =>
    cases annotated with
    | nil => exact ⟨fun _ => .nil,fun _ => by simp [validateMany]⟩
    | cons a ts =>
      exact ⟨fun h => by simp [validateMany] at h,fun h => by cases h⟩
  | cons head rest =>
    cases annotated with
    | nil => exact ⟨fun h => by simp [validateMany] at h,fun h => by cases h⟩
    | cons first later =>
      rw [validateMany,Bool.and_eq_true,validates exactHere head first,validates_many exactHere rest later]
      exact ⟨fun ⟨one,tail⟩ => .cons one tail,fun proof => by
        cases proof with | cons one tail => exact ⟨one,tail⟩⟩
termination_by sizeOf annotated
end

end Yulang.GeneralDeclarativeFiniteCheck327
