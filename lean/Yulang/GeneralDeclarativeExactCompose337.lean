import Yulang.GeneralDeclarativeExactDelete337

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativeExactCompose337
open GeneralDeclarativeExactDelete337 (subtract recordShell)
open GeneralDeclarativeExactDeleteFinite337 (remaining)
open CommonNominalFullCarrier (Ty)

theorem remaining_compose (first last marked : List Nat) :
    remaining first (remaining last marked) = remaining (first ++ last) marked := by
  simp [remaining,List.filter_filter,List.contains_append,Bool.not_or]

theorem shell_idempotent (ty : Ty) : recordShell (recordShell ty) = recordShell ty := by
  induction ty <;> simp [recordShell, *]

theorem shell_commutes (keys : List Nat) (ty : Ty) :
    subtract keys (recordShell ty) = recordShell (subtract keys ty) := by
  induction ty with
  | union a b first last => simp [recordShell,subtract,first,last]
  | inter a b first last => simp [recordShell,subtract,first,last]
  | mask hs a rest => simp [recordShell,subtract,rest]
  | bottom =>
    by_cases gone : 0 ∈ keys <;> simp [recordShell,subtract,gone]
  | record k p a _ =>
    by_cases gone : k ∈ keys <;> simp [recordShell,subtract,gone,shell_idempotent]
  | recordDefault k a p _ =>
    by_cases gone : k ∈ keys <;> simp [recordShell,subtract,gone,shell_idempotent]
  | _ => rfl

/-- Nested standalone cuts compose on actual carrier types. The law
is a structural equality, not only observational equivalence after
masking. Reusing or repeating a removed label does not lose absence. -/
theorem sequence (first last : List Nat) (ty : Ty) :
    subtract first (subtract last ty) = subtract (first ++ last) ty := by
  induction ty with
  | union a b left right => simp [subtract,left,right]
  | inter a b left right => simp [subtract,left,right]
  | mask hs a rest => simp [subtract,remaining_compose,rest]
  | record k p a ih =>
    by_cases h : k ∈ last
    · have together : k ∈ first ++ last := List.mem_append_right _ h
      simp [subtract,h,together,shell_commutes,ih]
    · by_cases j : k ∈ first
      · have together : k ∈ first ++ last := List.mem_append_left _ j
        simp [subtract,h,j,together,ih]
      · have together : k ∉ first ++ last := fun hit => (List.mem_append.mp hit).elim j h
        simp [subtract,h,j,together,ih]
  | recordDefault k a p ih =>
    by_cases h : k ∈ last
    · have together : k ∈ first ++ last := List.mem_append_right _ h
      simp [subtract,h,together,shell_commutes,ih]
    · by_cases j : k ∈ first
      · have together : k ∈ first ++ last := List.mem_append_left _ j
        simp [subtract,h,j,together,ih]
      · have together : k ∉ first ++ last := fun hit => (List.mem_append.mp hit).elim j h
        simp [subtract,h,j,together,ih]
  | _ => rfl

theorem empty (t : Ty) : subtract [] t = t := by
  induction t <;> simp [subtract,remaining, *]

end Yulang.GeneralDeclarativeExactCompose337
