import Yulang.GeneralNominalCenteredHeadMatExtension
import Yulang.CommonNominalFullConstructors
import Yulang.CommonRoleOutermostResolver

/-! Total materialized expressions respect semantic equivalence, including
invariant nominal arguments. No injectivity assumption is introduced. -/
namespace Yulang.GeneralDictionaryDefaultExpression209
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCenteredHeadMatExtension (names namesMany)
open CommonNominalFullCarrier
open CommonRoleOutermostResolver (All₂)

 theorem equivalent_refl (type : Ty) : Equivalent type type := ⟨subtype_refl _,subtype_refl _⟩
 theorem equivalent_trans (one : Equivalent first middle) (two : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

 theorem primitive_equivalent (constructor : GeneralCandidateInspection.Primitive)
    (same : All₂ Equivalent first last) :
    Equivalent (primitiveValue constructor first) (primitiveValue constructor last) := by
  cases constructor with
  | scalar base =>
      cases same with
      | nil => exact equivalent_refl _
      | cons => exact equivalent_refl _
  | emptyRecord =>
      cases same with
      | nil => exact equivalent_refl _
      | cons => exact equivalent_refl _
  | exactEmpty =>
      cases same with
      | nil => exact equivalent_refl _
      | cons => exact equivalent_refl _
  | pair =>
      cases same with
      | nil => exact equivalent_refl _
      | cons a rest =>
          cases rest with
          | nil => exact equivalent_refl _
          | cons b tail =>
              cases tail with
              | nil => exact ⟨(common_pair_iff _ _ _ _).mpr ⟨a.1,b.1⟩,
                  (common_pair_iff _ _ _ _).mpr ⟨a.2,b.2⟩⟩
              | cons => exact equivalent_refl _

 theorem list_length (same : All₂ Equivalent first last) : first.length = last.length := by
  induction same with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

 theorem list_get {index : Nat} (same : All₂ Equivalent first last)
    (left : first[index]? = some a) (right : last[index]? = some b) : Equivalent a b := by
  induction same generalizing index with
  | nil => simp at left
  | @cons a₀ b₀ as bs pair rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at left right
          exact left ▸ right ▸ pair
      | succ index => exact ih left right

 theorem list_symm (same : All₂ Equivalent first last) : All₂ Equivalent last first := by
  induction same with
  | nil => exact .nil
  | cons pair rest ih => exact .cons ⟨pair.2,pair.1⟩ ih

 theorem nominal_equivalent (name : Nat) (same : All₂ Equivalent first last) :
    Equivalent (nominal name (first.map Sum.inl)) (nominal name (last.map Sum.inl)) := by
  have order {a b : List Ty} (paired : All₂ Equivalent a b) :
      Subtype (nominal name (a.map Sum.inl)) (nominal name (b.map Sum.inl)) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,by simpa only [List.length_map] using list_length paired,?_⟩
    intro index x y left right
    obtain ⟨xx,atX,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using left)
    obtain ⟨yy,atY,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using right)
    exact list_get paired atX atY
  exact ⟨order same,order (list_symm same)⟩

mutual
 theorem value_equivalent (expression : Expr)
    (agree : ∀ mode name, name ∈ names expression → Equivalent (first mode name) (last mode name)) :
    Equivalent (value first mode expression) (value last mode expression) := by
  cases expression with
  | «variable» name => exact agree mode name (List.mem_singleton_self _)
  | primitive constructor arguments => exact primitive_equivalent constructor (values_equivalent arguments agree)
  | nominal name arguments => exact nominal_equivalent name (values_equivalent arguments agree)
  | record label payload tail =>
      have a := value_equivalent (mode := mode) payload (fun m n h => agree m n (List.mem_append_left _ h))
      have b := value_equivalent (mode := mode) tail (fun m n h => agree m n (List.mem_append_right _ h))
      exact ⟨common_record_mono label a.1 b.1,common_record_mono label a.2 b.2⟩
  | variant tag payload =>
      have a := value_equivalent (mode := mode) payload agree
      exact ⟨(common_variant_iff tag _ _).mpr a.1,(common_variant_iff tag _ _).mpr a.2⟩
  | join a b =>
      have one := value_equivalent (mode := mode) a (fun m n h => agree m n (List.mem_append_left _ h))
      have two := value_equivalent (mode := mode) b (fun m n h => agree m n (List.mem_append_right _ h))
      exact ⟨common_union_mono one.1 two.1,common_union_mono one.2 two.2⟩
 theorem values_equivalent (expressions : List Expr)
    (agree : ∀ mode name, name ∈ namesMany expressions → Equivalent (first mode name) (last mode name)) :
    All₂ Equivalent (values first mode expressions) (values last mode expressions) := by
  cases expressions with
  | nil => exact .nil
  | cons head rest =>
      exact .cons
        (value_equivalent head (fun m n h => agree m n (List.mem_append_left _ h)))
        (values_equivalent rest (fun m n h => agree m n (List.mem_append_right _ h)))
end
end Yulang.GeneralDictionaryDefaultExpression209
