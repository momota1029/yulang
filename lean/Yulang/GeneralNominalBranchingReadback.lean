import Yulang.GeneralNominalGroundProduction
import Yulang.GeneralNominalPeelingOrigins

/-! Every observed nominal or pair projection of a finite constructor tree
has a finite subtree value. The path is produced independently of the tree. -/
namespace Yulang.GeneralNominalBranchingReadback
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

inductive Tree where
  | scalar (base : Inference.Base)
  | pair (first last : Tree)
  | nominal (name : Nat) (children : List Tree)

mutual
  def Tree.value : Tree → Ty
    | .scalar base => .base base
    | .pair first last => CommonNominalFullCarrier.pair first.value last.value
    | .nominal name children => CommonNominalFullCarrier.nominal name (values children)
  def values : List Tree → List Argument
    | [] => []
    | child :: rest => .inl child.value :: values rest
end

mutual
  def Tree.mass : Tree → Nat
    | .scalar _ => 1
    | .pair first last => 1 + first.mass + last.mass
    | .nominal _ children => 1 + masses children
  def masses : List Tree → Nat
    | [] => 0
    | child :: rest => child.mass + masses rest
end

theorem values_length (children : List Tree) : (values children).length = children.length := by
  induction children <;> simp_all [values]

theorem values_at (children : List Tree) {index : Nat} {child : Tree} (member : children[index]? = some child) :
    (values children)[index]? = some (.inl child.value) := by
  induction children generalizing index with
  | nil => simp at member
  | cons head rest ih =>
    cases index with
    | zero => cases Option.some.inj member; rfl
    | succ index => exact ih member

theorem member_mass (children : List Tree) {child : Tree} (member : child ∈ children) : child.mass ≤ masses children := by
  induction children with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [masses]; omega
    · have bound := ih member; simp only [masses]; omega

theorem scalar_not_pair (base : Inference.Base) (first last : Ty) :
    ¬ Subtype (.base base) (CommonNominalFullCarrier.pair first last) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.pairFirst .trivial) trivial

theorem nominal_not_pair (name : Nat) (arguments : List Argument) (first last : Ty) :
    ¬ Subtype (CommonNominalFullCarrier.nominal name arguments) (CommonNominalFullCarrier.pair first last) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.pairFirst .trivial) trivial

theorem pair_not_nominal (first last : Ty) (name : Nat) (arguments : List Argument) :
    ¬ Subtype (CommonNominalFullCarrier.pair first last) (CommonNominalFullCarrier.nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

inductive Path (root : Origin) : Nat → Origin → Prop
  | root : Path root 0 root
  | nominal : Path root depth parent → Path root (depth+1) (.nominal parent name index)
  | pair (index : Fin 2) : Path root depth parent → Path root (depth+1) (.structural parent .pair index.val)

theorem nominal_child (tree : Tree) {index : Nat} (equal : Equivalent value tree.value)
    (head : Equivalent value (CommonNominalFullCarrier.nominal name arguments))
    (found : arguments[index]? = some (.inl actual)) :
    ∃ child : Tree, child.mass < tree.mass ∧ Equivalent actual child.value := by
  cases tree with
  | scalar base => exact False.elim (GeneralNominalPeelingOrigins.base_not_nominal base name arguments
      (subtype_trans equal.2 head.1))
  | pair first last => exact False.elim (pair_not_nominal first.value last.value name arguments
      (subtype_trans equal.2 head.1))
  | nominal label children =>
    have same := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 head.1)
    have bound : index < children.length := by
      have present := (List.getElem?_eq_some_iff.mp found).1
      rw [← same.2.1,values_length] at present
      exact present
    let child := children[index]
    have atChild : children[index]? = some child := List.getElem?_eq_getElem bound
    have childEqual := same.2.2 index (.inl child.value) (.inl actual) (values_at children atChild) found
    have smaller : child.mass ≤ masses children := member_mass children (List.getElem_mem bound)
    exact ⟨child,by simp only [Tree.mass]; omega,⟨childEqual.2,childEqual.1⟩⟩

theorem pair_child (tree : Tree) (equal : Equivalent value tree.value)
    (length : xs.length = 2) (head : Equivalent value (shapeValue .pair xs))
    (index : Fin 2) (found : xs[index.val]? = some actual) :
    ∃ child : Tree, child.mass < tree.mass ∧ Equivalent actual child.value := by
  cases tree with
  | scalar base => exact False.elim (scalar_not_pair base _ _ (subtype_trans equal.2 head.1))
  | nominal label children => exact False.elim (nominal_not_pair label _ _ _ (subtype_trans equal.2 head.1))
  | pair first last =>
    have payload := GeneralNominalStructuralReadback.shape_payload .pair trivial xs
      [first.value,last.value] length rfl found
      (show [first.value,last.value][index.val]? = some (if index.val = 0 then first.value else last.value) by
        have small := index.isLt
        have cases : index.val = 0 ∨ index.val = 1 := by omega
        rcases cases with h | h <;> simp [h])
      ⟨subtype_trans head.2 equal.1,subtype_trans equal.2 head.1⟩
    by_cases zero : index.val = 0
    · exact ⟨first,by simp only [Tree.mass]; omega,by simpa only [zero,ite_true] using payload⟩
    · exact ⟨last,by simp only [Tree.mass]; omega,by simpa only [zero,ite_false] using payload⟩

theorem observed_path {model : GeneralNominalCommonBridge.Assignment} (path : Path root depth origin) (tree : Tree)
    (initial : ∀ value, Observes model root value → Equivalent value tree.value)
    (seen : Observes model origin actual) :
    ∃ part : Tree, depth + part.mass ≤ tree.mass ∧ Equivalent actual part.value := by
  induction path generalizing actual with
  | root => exact ⟨tree,by omega,initial actual seen⟩
  | nominal prior ih =>
    cases seen with
    | nominal parent head found =>
      obtain ⟨part,bound,equal⟩ := ih parent
      obtain ⟨child,small,meaning⟩ := nominal_child part equal head found
      exact ⟨child,by omega,meaning⟩
  | pair index prior ih =>
    cases seen with
    | structural parent length head found =>
      obtain ⟨part,bound,equal⟩ := ih parent
      obtain ⟨child,small,meaning⟩ := pair_child part equal length head index found
      exact ⟨child,by omega,meaning⟩

end Yulang.GeneralNominalBranchingReadback
