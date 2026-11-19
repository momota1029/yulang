import Yulang.GeneralRebaseUnaryRank271
import Yulang.GeneralNominalFiniteHeadInversion

namespace Yulang.GeneralRebaseFiniteTree272
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Test Origin)
open GeneralNominalOriginTerms (arity project)
open GeneralNominalFiniteMeaning (At build project_value)
open GeneralNominalReadbackFunctionality (TestCanonical)
open GeneralNominalCommonBridge (Assignment)

inductive Tree where
 | node (test : Test) (children : Fin (arity test) → Tree)

def Canonical : Tree → Prop
 | .node test children => TestCanonical test ∧ ∀ i, Canonical (children i)

def value : Tree → Ty
 | .node test children => build test (fun i => value (children i))

def height : Tree → Nat
 | .node _ children => 1 + (List.ofFn fun i => height (children i)).foldr max 0

theorem list_height (xs : List Nat) (v : Nat) (seen : v ∈ xs) : v ≤ xs.foldr max 0 := by
 induction xs with
 | nil => cases seen
 | cons head tail ih =>
   rcases List.mem_cons.mp seen with rfl | h
   · exact Nat.le_max_left ..
   · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

theorem child_height (test : Test) (children : Fin (arity test) → Tree) (i : Fin (arity test)) :
 height (children i) < height (.node test children) := by
 have found : height (children i) ∈ List.ofFn (fun j => height (children j)) := List.mem_ofFn.mpr ⟨i,rfl⟩
 have h := list_height _ _ found
 change height (children i) < 1 + (List.ofFn fun j => height (children j)).foldr max 0
 omega

theorem at_agree (m : Assignment) (o : Origin) (x y : Ty) (first : At m .actual o x)
 (last : At m .actual o y) : Equivalent x y := by
 obtain ⟨v,found⟩ := first.1
 have a := first.2 v found
 have b := last.2 v found
 exact ⟨subtype_trans a.2 b.1,subtype_trans b.2 a.1⟩

theorem children_agree (test : Test) (canonical : TestCanonical test) (a b : Fin (arity test) → Ty)
 (same : Equivalent (build test a) (build test b)) (i : Fin (arity test)) :
 Equivalent (a i) (b i) := by
 let m : Assignment := fun _ => (build test a,Common.rowEmpty)
 let o : Origin := .source 0
 have left := GeneralRebaseInstalledReadback271.source_at m 0 (build test a) ⟨subtype_refl _,subtype_refl _⟩
 have right := GeneralRebaseInstalledReadback271.source_at m 0 (build test b) same
 exact at_agree m (project o test i) _ _ (project_value test canonical a left i) (project_value test canonical b right i)

theorem height_invariant (a b : Tree) (one : Canonical a) (two : Canonical b)
 (same : Equivalent (value a) (value b)) : height a = height b := by
 induction a generalizing b with
 | node t children ih =>
   cases b with
   | node other rest =>
     have key := GeneralNominalFiniteHeadInversion.test_equal t other (fun i => value (children i))
       (fun j => value (rest j)) one.1 two.1 same
     subst other
     have all (i : Fin (arity t)) : height (children i) = height (rest i) :=
       ih i _ (one.2 i) (two.2 i) (children_agree t one.1 _ _ same i)
     change 1 + (List.ofFn fun i => height (children i)).foldr max 0 =
       1 + (List.ofFn fun i => height (rest i)).foldr max 0
     rw [show (fun i => height (children i)) = (fun i => height (rest i)) from funext all]

def scalar (base : Inference.Base) : Tree := .node (.scalar base) Fin.elim0

end Yulang.GeneralRebaseFiniteTree272
