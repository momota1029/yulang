import Std
/-! A standalone syntax-only diagnostic. These are not language transitions.
Two individually external substitutions over two names need not bound retained
consumer syntax. No reachable Yulang state or semantic failure is asserted. -/
namespace Yulang.GeneralNominalRebaseSyntaxGrowth244
inductive Name where
 | first | second
 deriving DecidableEq
inductive Expr where
 | var (name : Name)
 | join (first last : Expr)
 deriving DecidableEq
open Expr

def sources : Expr → List Name
 | .var name => [name]
 | .join first last => sources first ++ sources last

def substitute (target : Name) (replacement : Expr) : Expr → Expr
 | .var name => if name = target then replacement else .var name
 | .join first last => .join (substitute target replacement first) (substitute target replacement last)

def firstBlock : Expr := .join (.var .second) (.var .second)
def secondBlock : Expr := .join (.var .first) (.var .first)
theorem first_external : Name.first ∉ sources firstBlock := by decide
theorem second_external : Name.second ∉ sources secondBlock := by decide

def tree (name : Name) : Nat → Expr
 | 0 => .var name
 | n+1 => .join (tree name n) (tree name n)
def height : Expr → Nat
 | .var _ => 0
 | .join first last => max (height first) (height last) + 1

def round (term : Expr) : Expr :=
 substitute .second secondBlock (substitute .first firstBlock term)
def iterate : Nat → Expr
 | 0 => .var .first
 | n+1 => round (iterate n)

theorem first_tree (depth : Nat) : substitute .first firstBlock (tree .first depth) = tree .second (depth+1) := by
 induction depth with
 | zero => rfl
 | succ depth ih => simp only [tree,substitute,ih]
theorem second_tree (depth : Nat) : substitute .second secondBlock (tree .second depth) = tree .first (depth+1) := by
 induction depth with
 | zero => rfl
 | succ depth ih => simp only [tree,substitute,ih]
theorem iterate_tree (n : Nat) : iterate n = tree .first (2*n) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [iterate,round,ih,first_tree,second_tree]
   congr 1
theorem tree_height (name : Name) (depth : Nat) : height (tree name depth) = depth := by
 induction depth with
 | zero => rfl
 | succ depth ih => simp only [tree,height,ih,Nat.max_self]
theorem iterate_height (n : Nat) : height (iterate n) = 2*n := by rw [iterate_tree,tree_height]
theorem no_height_bound : ∀ bound, ∃ n, bound < height (iterate n) := by
 intro bound
 refine ⟨bound+1,?_⟩
 rw [iterate_height]
 omega

theorem finite_sources (term : Expr) : sources term ⊆ [Name.first,Name.second] := by
 intro name _
 cases name <;> simp
theorem iterate_injective : Function.Injective iterate := by
 intro first last same
 have equal := congrArg height same
 rw [iterate_height,iterate_height] at equal
 omega

def bound (terms : List Expr) : Nat := (terms.map height).foldr max 0

theorem height_le_bound (member : term ∈ terms) : height term ≤ bound terms := by
 induction terms with
 | nil => cases member
 | cons head rest ih =>
   rcases List.mem_cons.mp member with rfl | later
   · exact Nat.le_max_left _ _
   · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

theorem no_finite_syntax_pool (terms : List Expr) : ∃ n, iterate n ∉ terms := by
 obtain ⟨n,larger⟩ := no_height_bound (bound terms)
 exact ⟨n,fun present => Nat.not_lt_of_ge (height_le_bound present) larger⟩
end Yulang.GeneralNominalRebaseSyntaxGrowth244
