import Yulang.GeneralRebaseTreeInterpreter272

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTreeConstructors272
open CommonNominalFullCarrier
open GeneralRebaseFiniteTree272 (Tree Canonical value scalar)
open GeneralNominalFiniteMeaning (build)
open GeneralNominalRecursiveInspection (shapeValue)
open GeneralNormalizedObservation (Shape)

def nominalTree (name : Nat) (xs : List Tree) : Tree :=
 .node (.nominal name xs.length) (fun i => xs[i.val]'(i.isLt))

theorem nominal_tree_canonical (name : Nat) (xs : List Tree) (checked : ∀ x ∈ xs, Canonical x) :
 Canonical (nominalTree name xs) :=
 ⟨True.intro,fun i => checked _ (List.getElem_mem i.isLt)⟩

theorem nominal_value (name : Nat) (xs : List Tree) :
 value (nominalTree name xs) = nominal name (xs.map fun x => .inl (value x)) := by
 change nominal name (List.ofFn (fun i : Fin xs.length => (.inl (value xs[i]) : Argument))) = _
 apply congrArg (nominal name)
 apply List.ext_getElem
 · simp
 · intro index one two
   simp only [List.getElem_ofFn,List.getElem_map]
   rfl

def pairTree (a b : Tree) : Tree :=
 .node (.structural .pair) (fun i => if i.val = 0 then a else b)

theorem pair_checked (a b : Tree) (x : Canonical a) (y : Canonical b) :
 Canonical (pairTree a b) :=
 ⟨True.intro,fun i => by change Canonical (if i.val = 0 then a else b); split; exact x; exact y⟩

theorem pair_value (x y : Tree) : value (pairTree x y) = pair (value x) (value y) := rfl

def variantTree (tag : Nat) (child : Tree) : Tree :=
 .node (.structural (.variant tag)) fun _ => child

theorem variant_checked (tag : Nat) (child : Tree) (good : Canonical child) :
 Canonical (variantTree tag child) := ⟨True.intro,fun _ => good⟩

theorem variant_value (tag : Nat) (child : Tree) : value (variantTree tag child) = variant tag (value child) := rfl

def emptyTree : Tree := .node (.structural .exactEmpty) Fin.elim0

theorem empty_canonical : Canonical emptyTree := ⟨True.intro,fun i => Fin.elim0 i⟩

def recordTree (keys : List Nat) (children : Fin keys.length → Tree) : Tree :=
 .node (.structural (.record keys)) children

theorem record_canonical (keys : List Nat) (can : keys.Pairwise (· < ·))
 (children : Fin keys.length → Tree) (all : ∀ i, Canonical (children i)) :
 Canonical (recordTree keys children) := ⟨can,all⟩

theorem record_value (keys : List Nat) (children : Fin keys.length → Tree) :
 value (recordTree keys children) =
 GeneralNominalStructuralReadback.recordValues (keys.zip (List.ofFn (fun j => value (children j)))) :=
 GeneralNominalRecordInversion.record_shape keys _ (List.length_ofFn ..)

theorem scalar_canonical (base : Inference.Base) : Canonical (scalar base) :=
 ⟨True.intro,fun i => Fin.elim0 i⟩

end Yulang.GeneralRebaseTreeConstructors272
