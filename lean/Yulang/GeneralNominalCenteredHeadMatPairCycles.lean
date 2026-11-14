import Yulang.GeneralNominalCenteredHeadMatStepCycles
import Yulang.GeneralNominalBranchingMass
import Yulang.GeneralNominalFiniteHeadInversion

namespace Yulang.GeneralNominalCenteredHeadMatPairCycles
open GeneralNominalRecursiveInspection GeneralNominalBranchingReadback
open GeneralNominalOriginTerms (arity project)
open GeneralNominalFiniteMeaning (build)
open GeneralNominalFiniteHeadInversion (head equivalent_head)
open CommonNominalFullCarrier
variable {model : GeneralNominalCommonBridge.Assignment} {values : List Ty} {index : Nat}

def PairTree : Tree → Prop
  | .scalar _ => True
  | .pair first last => PairTree first ∧ PairTree last
  | .nominal _ _ => False

theorem not_nominal (tree : Tree) (pure : PairTree tree)
    (equal : Equivalent value tree.value) (nominalHead : Equivalent value (nominal name arguments)) : False := by
  cases tree with
  | scalar base => exact GeneralNominalPeelingOrigins.base_not_nominal base name arguments (subtype_trans equal.2 nominalHead.1)
  | pair first last => exact pair_not_nominal first.value last.value name arguments (subtype_trans equal.2 nominalHead.1)
  | nominal => exact pure

theorem shape_build (length : values.length = shape.arity) :
    shapeValue shape values = build (.structural shape)
      (fun index => values[index.val]'(length.symm ▸ index.isLt)) := by
  unfold build
  congr 1
  apply List.ext_getElem (by simp [length,arity])
  intro index one two
  simp

theorem pair_shape (length : values.length = shape.arity)
    (equal : Equivalent (pair first last) (shapeValue shape values)) : shape = .pair := by
  rw [shape_build length] at equal
  have heads := equivalent_head (.structural .pair) (.structural shape)
    (fun i => if i.val = 0 then first else last) _ equal
  cases shape <;> first | rfl | cases heads

theorem scalar_no_shape (length : values.length = shape.arity)
    (equal : Equivalent (.base base) (shapeValue shape values)) : False := by
  rw [shape_build length] at equal
  have heads := equivalent_head (.scalar base) (.structural shape) Fin.elim0 _ equal
  cases shape <;> cases heads

theorem structural_child (tree : Tree) (pure : PairTree tree)
    (equal : Equivalent value tree.value) (length : values.length = shape.arity)
    (shapeHead : Equivalent value (shapeValue shape values)) (found : values[index]? = some actual) :
    ∃ child : Tree, PairTree child ∧ child.mass < tree.mass ∧ Equivalent actual child.value := by
  have compared : Equivalent tree.value (shapeValue shape values) :=
    ⟨subtype_trans equal.2 shapeHead.1,subtype_trans shapeHead.2 equal.1⟩
  cases tree with
  | scalar base => exact False.elim (scalar_no_shape length compared)
  | nominal => exact False.elim pure
  | pair first last =>
      have shapeEq := pair_shape length compared
      subst shape
      have bounded : index < 2 := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        rw [length] at bound
        exact bound
      have located : [first.value,last.value][index]? = some (if index = 0 then first.value else last.value) := by
        have cases : index = 0 ∨ index = 1 := by omega
        rcases cases with rfl | rfl <;> rfl
      have payload := GeneralNominalStructuralReadback.shape_payload .pair trivial values [first.value,last.value]
        length rfl found located ⟨compared.2,compared.1⟩
      by_cases zero : index = 0
      · exact ⟨first,pure.1,by simp [Tree.mass]; omega,by simpa [zero] using payload⟩
      · exact ⟨last,pure.2,by simp [Tree.mass]; omega,by simpa [zero] using payload⟩

theorem observed_tree (source : ∀ identity, ∃ tree : Tree, PairTree tree ∧ (model identity).1 = tree.value)
    (seen : Observes model origin actual) : ∃ tree : Tree, PairTree tree ∧ Equivalent actual tree.value := by
  induction seen with
  | source identity =>
      obtain ⟨tree,pure,equal⟩ := source identity
      exact ⟨tree,pure,equal ▸ ⟨subtype_refl _,subtype_refl _⟩⟩
  | nominal parent nominalHead found ih =>
      obtain ⟨tree,pure,equal⟩ := ih
      exact False.elim (not_nominal tree pure equal nominalHead)
  | structural parent length shapeHead found ih =>
      obtain ⟨tree,pure,equal⟩ := ih
      obtain ⟨child,pure,_,meaning⟩ := structural_child tree pure equal length shapeHead found
      exact ⟨child,pure,meaning⟩

theorem projected_smaller (tree : Tree) (pure : PairTree tree)
    (same : ∀ value, Observes model origin value → Equivalent value tree.value)
    (test : Test) (index : Fin (arity test)) (seen : Observes model (project origin test index) actual) :
    ∃ child : Tree, PairTree child ∧ child.mass < tree.mass ∧ Equivalent actual child.value := by
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal =>
      cases seen with
      | nominal parent nominalHead found => exact False.elim (not_nominal tree pure (same _ parent) nominalHead)
  | structural shape =>
      cases seen with
      | structural parent length shapeHead found => exact structural_child tree pure (same _ parent) length shapeHead found

def Describes (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) (tree : Tree) : Prop :=
  PairTree tree ∧ ∃ actual, Observes model origin actual ∧ Equivalent actual tree.value

noncomputable def mass (model : GeneralNominalCommonBridge.Assignment) (origin : Origin) : Nat := by
  classical
  exact if found : ∃ tree, Describes model origin tree then (Classical.choose found).mass else 0

theorem mass_eq (meaning : Describes model origin tree)
    (unique : GeneralNominalReadbackFunctionality.Unique model origin) : mass model origin = tree.mass := by
  classical
  have found : ∃ tree, Describes model origin tree := ⟨tree,meaning⟩
  rw [mass,dite_eq_left found]
  obtain ⟨_,first,seenFirst,equalFirst⟩ := Classical.choose_spec found
  obtain ⟨_,last,seenLast,equalLast⟩ := meaning
  have same := unique first last seenFirst seenLast
  exact GeneralNominalBranchingMass.equivalent_mass _ _
    ⟨subtype_trans equalFirst.2 (subtype_trans same.1 equalLast.1),
      subtype_trans equalLast.2 (subtype_trans same.2 equalFirst.1)⟩

theorem edge_decreases (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (source : ∀ identity, ∃ tree : Tree, PairTree tree ∧ (model identity).1 = tree.value)
    (edge : GeneralNominalCenteredHeadMatStepCycles.Edge state first last) : mass model last < mass model first := by
  obtain ⟨parent,test,index,_,one,two⟩ := edge
  have one := one model valid
  have two := two model valid
  obtain ⟨firstValue,seenFirst⟩ := one.1
  obtain ⟨firstTree,pureFirst,meaningFirst⟩ := observed_tree source seenFirst
  obtain ⟨projected,seenProjected⟩ := two.1
  have parentMeaning : ∀ value, Observes model parent value → Equivalent value firstTree.value := by
    intro value observed
    have same := one.2.2 firstValue value seenFirst observed
    exact ⟨subtype_trans same.2 meaningFirst.1,subtype_trans meaningFirst.2 same.1⟩
  obtain ⟨lastTree,pureLast,smaller,meaningLast⟩ := projected_smaller firstTree pureFirst parentMeaning test index seenProjected
  obtain ⟨lastValue,seenLast⟩ := two.2.1
  have equalLast := two.2.2 projected lastValue seenProjected seenLast
  have lastMeaning : Equivalent lastValue lastTree.value :=
    ⟨subtype_trans equalLast.2 meaningLast.1,subtype_trans meaningLast.2 equalLast.1⟩
  have uniqueFirst : GeneralNominalReadbackFunctionality.Unique model first := by
    obtain ⟨value,seen⟩ := one.2.1
    intro a b sa sb
    exact ⟨subtype_trans (one.2.2 a value sa seen).1 (one.2.2 b value sb seen).2,
      subtype_trans (one.2.2 b value sb seen).1 (one.2.2 a value sa seen).2⟩
  have uniqueLast : GeneralNominalReadbackFunctionality.Unique model last := by
    intro a b sa sb
    exact ⟨subtype_trans (two.2.2 projected a seenProjected sa).2 (two.2.2 projected b seenProjected sb).1,
      subtype_trans (two.2.2 projected b seenProjected sb).2 (two.2.2 projected a seenProjected sa).1⟩
  rw [mass_eq ⟨pureFirst,firstValue,seenFirst,meaningFirst⟩ uniqueFirst,
    mass_eq ⟨pureLast,lastValue,seenLast,lastMeaning⟩ uniqueLast]
  exact smaller

theorem acyclic (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (source : ∀ identity, ∃ tree : Tree, PairTree tree ∧ (model identity).1 = tree.value) (origin) :
    ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic state origin := by
  have paths : ∀ a b, GeneralNominalCenteredHeadMatStepCycles.Path state a b → mass model b ≤ mass model a := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_decreases valid source edge))
  rintro ⟨⟨next,edge,path⟩,_⟩
  have smaller := edge_decreases valid source edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralNominalCenteredHeadMatPairCycles
