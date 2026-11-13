import Yulang.GeneralNominalSharedSupport

/-! Finite symbolic enumeration and substitution bounds. The constructor and
leaf lists and the depth bound are explicit; their source derivation is separate. -/
namespace Yulang.GeneralNominalSharedEnumeration
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection

def choices (values : List α) : (count : Nat) → List (Fin count → α)
  | 0 => [Fin.elim0]
  | count+1 => values.flatMap fun first =>
      (choices values count).map fun rest => Fin.cases first rest

theorem choices_complete (values : List α) (count : Nat) (assignment : Fin count → α)
    (included : ∀ index, assignment index ∈ values) : assignment ∈ choices values count := by
  induction count with
  | zero =>
      have equal : assignment = Fin.elim0 := funext fun index => Fin.elim0 index
      simp [choices,equal]
  | succ count ih =>
      have tail := ih (fun index => assignment index.succ) (fun index => included index.succ)
      have equal : Fin.cases (assignment 0) (fun index => assignment index.succ) = assignment := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      exact List.mem_flatMap.mpr ⟨assignment 0,included 0,
        List.mem_map.mpr ⟨_,tail,equal⟩⟩

inductive Bounded (leaves : List α) (tests : List Test) : Nat → Expr α → Prop
  | leaf (name : α) (depth : Nat) : name ∈ leaves → Bounded leaves tests depth (.leaf name)
  | node (test : Test) (children : Fin (arity test) → Expr α) : test ∈ tests →
      (∀ index, Bounded leaves tests depth (children index)) →
      Bounded leaves tests (depth+1) (.node test children)

def enumerate (leaves : List α) (tests : List Test) : Nat → List (Expr α)
  | 0 => leaves.map Expr.leaf
  | depth+1 => leaves.map Expr.leaf ++ tests.flatMap fun test =>
      (choices (enumerate leaves tests depth) (arity test)).map (Expr.node test)

theorem bounded_enumerated (bound : Bounded leaves tests depth term) :
    term ∈ enumerate leaves tests depth := by
  induction bound with
  | leaf name depth present =>
      cases depth with
      | zero => exact List.mem_map.mpr ⟨name,present,rfl⟩
      | succ depth => exact List.mem_append_left _ (List.mem_map.mpr ⟨name,present,rfl⟩)
  | node test children present bounded ih =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨test,present,
        List.mem_map.mpr ⟨children,choices_complete _ _ _ ih,rfl⟩⟩)

theorem bounded_mono (bound : Bounded leaves tests depth term) (larger : depth ≤ limit) :
    Bounded leaves tests limit term := by
  induction bound generalizing limit with
  | leaf name depth present => exact .leaf name limit present
  | @node depth test children present childrenBound ih =>
      cases limit with
      | zero => omega
      | succ limit => exact .node test children present (fun index => ih index (by omega))

theorem bounded_bind {names : List α} {leaves : List β} {term : Expr α}
    (bound : Bounded names tests depth term)
    (substitution : α → Expr β)
    (bounded : ∀ name ∈ names, Bounded leaves tests extra (substitution name)) :
    Bounded leaves tests (depth+extra) (term.bind substitution) := by
  induction bound with
  | leaf name depth present => exact bounded_mono (bounded name present) (by omega)
  | @node depth test children present childrenBound ih =>
      simpa only [Expr.bind,Nat.add_assoc,Nat.add_comm 1 extra] using
        (Bounded.node test (fun index => (children index).bind substitution) present ih)

/-- A bounded symbolic schema and bounded child/input substitutions produce
a member of one explicit finite list. No identity canonicalization is assumed. -/
theorem substituted_enumerated {names : List α} {leaves : List β} {term : Expr α}
    (bound : Bounded names tests depth term)
    (substitution : α → Expr β)
    (bounded : ∀ name ∈ names, Bounded leaves tests extra (substitution name)) :
    term.bind substitution ∈ enumerate leaves tests (depth+extra) :=
  bounded_enumerated (bounded_bind bound substitution bounded)

end Yulang.GeneralNominalSharedEnumeration
