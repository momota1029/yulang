import Yulang.GeneralSourceRoleTrack292

/-! Finite unresolved copy of a mixed Rowan child tree. Kinds are kept distinct
from token spelling and source position. This is not a Rust FFI exporter. -/
namespace Yulang.GeneralSourceRoleCstTree293

inductive Kind where
  | root | role | head | argument | indented | statement | typeDecl | binding
  | roleKw | pubKw | ourKw | myKw | typeKw | colon | equals
  | identifier | sigilIdentifier | whitespace | lineTrivia
  | missing | invalid | error | other
  deriving DecidableEq, Repr

inductive Tree where
  | token (kind : Kind) (text : String)
  | node (kind : Kind) (children : List Tree)
  deriving Repr

def Tree.kind : Tree → Kind
  | .token kind _ | .node kind _ => kind

abbrev Path := List Nat

def trivia : Tree → Bool
  | .token .whitespace _ | .token .lineTrivia _ => true
  | _ => false

/-- Keep the indices from the complete mixed child list. An ordinal in a
filtered list is not a CST child path. -/
def indexedFrom (i : Nat) : List Tree → List (Nat × Tree)
  | [] => []
  | x :: xs => (i,x) :: indexedFrom (i+1) xs

def significant (children : List Tree) : List (Nat × Tree) :=
  (indexedFrom 0 children).filter fun p => !(trivia p.2)

theorem indexed_exact {children : List Tree} {i j : Nat} {tree : Tree} :
    (j,tree) ∈ indexedFrom i children ↔ ∃ n, j = i+n ∧ children[n]? = some tree := by
  induction children generalizing i j tree with
  | nil => simp [indexedFrom]
  | cons x xs ih =>
    constructor
    · intro member
      rcases List.mem_cons.mp member with eq | next
      · have h := Prod.mk.inj eq
        exact ⟨0,by omega,by simpa using congrArg some h.2.symm⟩
      · obtain ⟨n,found,atN⟩ := ih.mp next
        exact ⟨n+1,by omega,atN⟩
    · rintro ⟨n,e,atN⟩
      cases n with
      | zero =>
        have tx := Option.some.inj atN
        apply List.mem_cons.mpr
        left
        exact Prod.ext (by omega) tx.symm
      | succ n =>
        apply List.mem_cons.mpr
        right
        exact ih.mpr ⟨n,by omega,atN⟩

theorem significant_exact {children : List Tree} {i : Nat} {t : Tree} :
    (i,t) ∈ significant children ↔ children[i]? = some t ∧ trivia t = false := by
  unfold significant
  rw [List.mem_filter]
  constructor
  · rintro ⟨h,clean⟩
    obtain ⟨n,same,read⟩ := indexed_exact.mp h
    have eq : i = n := by omega
    subst i
    exact ⟨by simpa using read,by simpa using clean⟩
  · rintro ⟨read,clean⟩
    exact ⟨indexed_exact.mpr ⟨i,by omega,read⟩,by simp [clean]⟩

end Yulang.GeneralSourceRoleCstTree293
