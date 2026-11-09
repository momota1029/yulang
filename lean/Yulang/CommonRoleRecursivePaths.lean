import Yulang.CommonRoleRecursiveConflicts
import Yulang.CommonRoleStructuralPaths

/-! Recursive same-head refutations lifted through actual directed paths. -/
namespace Yulang.CommonRoleRecursivePaths
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleSettledConstraints (State)
open CommonRoleStructuralPaths (Fact Path reach reach_exact path_subtype)
open CommonRoleRecursiveConflicts (Refutes refutes_no_subtype)
abbrev recursiveCheck (l r : TyTerm α) := CommonRoleRecursiveConflicts.check l r
theorem recursive_exact (l r : TyTerm α) : recursiveCheck l r = true ↔ Refutes l r :=
  CommonRoleRecursiveConflicts.check_exact l r
/-- Bounds may have arbitrary payloads; structural children are inspected recursively. -/
def Certificate (atoms : List (Atom (Fin n))) : Prop :=
  ∃ l r i j, Atom.tyLe l (.var i) ∈ atoms ∧ Atom.tyLe (.var j) r ∈ atoms ∧
    Path atoms i j ∧ Refutes l r

def pairCheck (paths : List (Fact n)) : Atom (Fin n) → Atom (Fin n) → Bool
  | .tyLe l (.var i), .tyLe (.var j) r => paths.contains (i,j) && recursiveCheck l r
  | _, _ => false

theorem pairCheck_exact (paths : List (Fact n)) (x y : Atom (Fin n)) :
    pairCheck paths x y = true ↔
    ∃ l r i j, x = .tyLe l (.var i) ∧ y = .tyLe (.var j) r ∧
      (i,j) ∈ paths ∧ Refutes l r := by
  cases x with
  | rowLe => cases y <;> simp [pairCheck]
  | tyLe l mid =>
    cases mid <;> cases y <;> simp [pairCheck]
    case var.tyLe i mid r =>
      cases mid <;> simp [recursive_exact]
      case var j =>
        grind

def pathCheck (atoms : List (Atom (Fin n))) : Bool :=
  let paths := reach atoms
  atoms.any fun l => atoms.any (pairCheck paths l)
theorem check_exact (atoms : List (Atom (Fin n))) : pathCheck atoms = true ↔ Certificate atoms := by
  simp only [pathCheck, List.any_eq_true]
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨l,r,i,j,rfl,rfl,hp,hm⟩ := (pairCheck_exact _ x y).mp h
    exact ⟨l,r,i,j,hx,hy,(reach_exact ..).mp hp,hm⟩
  · rintro ⟨l,r,i,j,hl,hr,hp,hm⟩
    exact ⟨_,hl,_,hr,(pairCheck_exact ..).mpr ⟨l,r,i,j,rfl,rfl,(reach_exact ..).mpr hp,hm⟩⟩
theorem certificate_no_model (atoms : List (Atom (Fin n))) (h : Certificate atoms)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a atoms := by
  intro models
  obtain ⟨l,r,i,j,hl,hr,hp,hm⟩ := h
  exact refutes_no_subtype l r hm a
    (Common.subtype_trans (models _ hl) (Common.subtype_trans (path_subtype atoms hp a models) (models _ hr)))
theorem checked_no_model (atoms : List (Atom (Fin n))) (h : pathCheck atoms = true)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a atoms :=
  certificate_no_model atoms ((check_exact atoms).mp h) a


def direct : Atom α → Bool
  | .tyLe l r => recursiveCheck l r
  | .rowLe _ _ => false

theorem direct_exact (x : Atom α) : direct x = true ↔
    ∃ l r, x = .tyLe l r ∧ Refutes l r := by
  cases x with
  | rowLe => simp [direct]
  | tyLe l r =>
    simp only [direct, recursive_exact]
    constructor
    · intro h; exact ⟨l,r,rfl,h⟩
    · rintro ⟨l',r',h,hm⟩; cases h; exact hm

def check (atoms : List (Atom (Fin n))) : Bool := atoms.any direct || pathCheck atoms

/-- Direct recursive refutation or refutation between path endpoints. -/
def AnyCertificate (atoms : List (Atom (Fin n))) : Prop :=
  (∃ l r, Atom.tyLe l r ∈ atoms ∧ Refutes l r) ∨ Certificate atoms

theorem check_all_exact (atoms : List (Atom (Fin n))) :
    check atoms = true ↔ AnyCertificate atoms := by
  simp only [check, Bool.or_eq_true, List.any_eq_true, direct_exact, check_exact, AnyCertificate]
  constructor
  · rintro (⟨x,hx,l,r,rfl,hr⟩ | hp)
    · exact Or.inl ⟨l,r,hx,hr⟩
    · exact Or.inr hp
  · rintro (⟨l,r,hm,hr⟩ | hp)
    · exact Or.inl ⟨_,hm,l,r,rfl,hr⟩
    · exact Or.inr hp

theorem checked_no_model_all (atoms : List (Atom (Fin n))) (h : check atoms = true)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a atoms := by
  intro hm
  simp only [check, Bool.or_eq_true] at h
  rcases h with hd | hp
  · obtain ⟨x,hx,h⟩ := List.any_eq_true.mp hd
    obtain ⟨l,r,rfl,hr⟩ := (direct_exact x).mp h
    exact refutes_no_subtype l r hr a (hm _ hx)
  · exact checked_no_model atoms hp a hm

def prune (states : List (State n)) : List (State n) := states.filter fun s => !check s.atoms

theorem prune_models (states : List (State n)) (a : Fin n → Comp Common.model) :
    (∃ s ∈ prune states, All Common.model a s.atoms) ↔
      ∃ s ∈ states, All Common.model a s.atoms := by
  constructor
  · rintro ⟨s,hs,hm⟩
    exact ⟨s,(List.mem_filter.mp hs).1,hm⟩
  · rintro ⟨s,hs,hm⟩
    refine ⟨s,List.mem_filter.mpr ⟨hs,?_⟩,hm⟩
    cases hc : check s.atoms
    · rfl
    · exact False.elim (checked_no_model_all s.atoms hc a hm)
/-- A same-head pair conflict invisible to outer-head inspection. -/
def nestedChain (x y z : TyTerm (Fin 3)) : List (Atom (Fin 3)) :=
  [.tyLe (.pair (.base .int) x) (.var 0), .tyLe (.var 0) (.var 1),
   .tyLe (.var 1) (.var 2), .tyLe (.var 2) (.pair (.pair y z) x)]

theorem nested_refutes (x y z : TyTerm α) :
    Refutes (.pair (.base .int) x) (.pair (.pair y z) x) := by
  apply CommonRoleRecursiveConflicts.Refutes.pairLeft
  apply CommonRoleRecursiveConflicts.Refutes.head
  exact (CommonRoleStructuralConflicts.mismatch_exact _ _).mp (by rfl)

theorem nested_chain_checked (x y z : TyTerm (Fin 3)) :
    check (nestedChain x y z) = true := by
  simp only [check, Bool.or_eq_true]
  right
  apply (check_exact _).mpr
  refine ⟨.pair (.base .int) x, .pair (.pair y z) x, 0, 2,
    by simp [nestedChain], by simp [nestedChain], ?_, nested_refutes x y z⟩
  have first : Path (nestedChain x y z) 0 1 := .step (.refl (i := 0)) (by simp [nestedChain])
  exact .step first (by simp [nestedChain])

theorem nested_outer_mismatch_false (x y z : TyTerm α) :
    CommonRoleStructuralConflicts.mismatch (.pair (.base .int) x) (.pair (.pair y z) x) = false := by
  rfl

theorem nested_chain_no_model (x y z : TyTerm (Fin 3)) (a : Fin 3 → Comp Common.model) :
    ¬ All Common.model a (nestedChain x y z) :=
  checked_no_model_all _ (nested_chain_checked x y z) a
end Yulang.CommonRoleRecursivePaths
