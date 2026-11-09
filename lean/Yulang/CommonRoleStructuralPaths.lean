import Yulang.CommonRoleStructuralConflicts

/-! Finite directed variable paths supporting rigid structural conflicts.
This checks outer heads, not general structural satisfiability. -/
namespace Yulang.CommonRoleStructuralPaths
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleStructuralConflicts (Mismatch mismatch mismatch_exact mismatch_no_subtype)
open CommonRoleDiagnosticEvidenceTransfer (edgeTest edgeTest_exact)
open CommonRoleSettledConstraints (State)

abbrev Fact (n : Nat) := Fin n × Fin n
def facts (n : Nat) : List (Fact n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i,j)
theorem facts_complete (f : Fact n) : f ∈ facts n := by
  rcases f with ⟨i,j⟩
  simp [facts]
theorem facts_length (n : Nat) : (facts n).length = n * n := by
  have sum_const (xs : List (Fin n)) : (xs.map (fun _ => n)).sum = xs.length * n := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa [facts] using sum_const (List.finRange n)
def edge (atoms : List (Atom (Fin n))) (i j : Fin n) : Bool := atoms.any (edgeTest i j)
theorem edge_exact (atoms : List (Atom (Fin n))) (i j : Fin n) :
    edge atoms i j = true ↔ Atom.tyLe (.var i) (.var j) ∈ atoms := by
  simp [edge, List.any_eq_true, edgeTest_exact]
inductive Path (atoms : List (Atom (Fin n))) : Fin n → Fin n → Prop where
  | refl : Path atoms i i
  | step : Path atoms i j → Atom.tyLe (.var j) (.var k) ∈ atoms → Path atoms i k

def reflRule (i : Fin n) : FiniteHorn.Rule (Fact n) := ⟨[],(i,i)⟩
def stepRule (i j k : Fin n) : FiniteHorn.Rule (Fact n) := ⟨[(i,j)],(i,k)⟩
def transfers (atoms : List (Atom (Fin n))) (i : Fin n) : List (FiniteHorn.Rule (Fact n)) :=
  ((facts n).filter fun jk => edge atoms jk.1 jk.2).map fun jk => stepRule i jk.1 jk.2
def rules (atoms : List (Atom (Fin n))) : List (FiniteHorn.Rule (Fact n)) :=
  (List.finRange n).map reflRule ++ (List.finRange n).flatMap (transfers atoms)
def reach (atoms : List (Atom (Fin n))) : List (Fact n) :=
  FiniteHorn.saturate (rules atoms) (facts n)

theorem reach_refl (atoms : List (Atom (Fin n))) (i : Fin n) : (i,i) ∈ reach atoms := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  exact ⟨reflRule i, List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩),rfl,by simp [reflRule]⟩
theorem reach_step (atoms : List (Atom (Fin n))) (h : (i,j) ∈ reach atoms)
    (e : Atom.tyLe (.var j) (.var k) ∈ atoms) : (i,k) ∈ reach atoms := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  refine ⟨stepRule i j k, List.mem_append_right _ ?_,rfl,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨(j,k),?_,rfl⟩⟩
    exact List.mem_filter.mpr ⟨facts_complete _,(edge_exact ..).mpr e⟩
  · simpa [stepRule,reach] using h

theorem rules_path (atoms : List (Atom (Fin n))) :
    ∀ rule ∈ rules atoms, FiniteHorn.Valid (fun f => Path atoms f.1 f.2) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with hr | ht
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact .refl
  · obtain ⟨i,_,h⟩ := List.mem_flatMap.mp ht
    unfold transfers at h
    obtain ⟨⟨j,k⟩,filtered,rfl⟩ := List.mem_map.mp h
    exact .step (premises (i,j) (by simp [stepRule]))
      ((edge_exact ..).mp (List.mem_filter.mp filtered).2)
theorem reach_exact (atoms : List (Atom (Fin n))) (i j : Fin n) :
    (i,j) ∈ reach atoms ↔ Path atoms i j := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_path atoms) (i,j)
  · intro h
    induction h with
    | refl => exact reach_refl atoms _
    | step _ e ih => exact reach_step atoms ih e
theorem reach_capacity (atoms : List (Atom (Fin n))) : (reach atoms).length ≤ n * n := by
  rw [← facts_length]
  exact FiniteHorn.saturate_length_le _ _ facts_complete
theorem reach_stopped (atoms : List (Atom (Fin n))) :
    FiniteHorn.firstFresh (rules atoms) (reach atoms) (facts n) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro f _ h
  exact FiniteHorn.saturate_closed _ _ facts_complete f h
theorem path_subtype (atoms : List (Atom (Fin n))) (h : Path atoms i j)
    (a : Fin n → Comp Common.model) (models : All Common.model a atoms) :
    Common.Subtype (a i).1 (a j).1 := by
  induction h with
  | refl => exact Common.subtype_refl _
  | step _ e ih => exact Common.subtype_trans ih (models _ e)

/-- Bounds may have arbitrary payloads; only their outer heads are inspected. -/
def Certificate (atoms : List (Atom (Fin n))) : Prop :=
  ∃ l r i j, Atom.tyLe l (.var i) ∈ atoms ∧ Atom.tyLe (.var j) r ∈ atoms ∧
    Path atoms i j ∧ Mismatch l r

def pairCheck (paths : List (Fact n)) : Atom (Fin n) → Atom (Fin n) → Bool
  | .tyLe l (.var i), .tyLe (.var j) r => paths.contains (i,j) && mismatch l r
  | _, _ => false

theorem pairCheck_exact (paths : List (Fact n)) (x y : Atom (Fin n)) :
    pairCheck paths x y = true ↔
    ∃ l r i j, x = .tyLe l (.var i) ∧ y = .tyLe (.var j) r ∧
      (i,j) ∈ paths ∧ Mismatch l r := by
  cases x with
  | rowLe => cases y <;> simp [pairCheck]
  | tyLe l mid =>
    cases mid <;> cases y <;> simp [pairCheck]
    case var.tyLe i mid r =>
      cases mid <;> simp [mismatch_exact]
      case var j =>
        grind

def check (atoms : List (Atom (Fin n))) : Bool :=
  let paths := reach atoms
  atoms.any fun l => atoms.any (pairCheck paths l)
theorem check_exact (atoms : List (Atom (Fin n))) : check atoms = true ↔ Certificate atoms := by
  simp only [check, List.any_eq_true]
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
  exact mismatch_no_subtype l r hm a
    (Common.subtype_trans (models _ hl) (Common.subtype_trans (path_subtype atoms hp a models) (models _ hr)))
theorem checked_no_model (atoms : List (Atom (Fin n))) (h : check atoms = true)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a atoms :=
  certificate_no_model atoms ((check_exact atoms).mp h) a

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
    · exact False.elim (checked_no_model s.atoms hc a hm)

/-- Three distinct slots separate the rigid bounds. -/
def chain (l r : TyTerm (Fin 3)) : List (Atom (Fin 3)) :=
  [.tyLe (.pair l r) (.var 0), .tyLe (.var 0) (.var 1),
   .tyLe (.var 1) (.var 2), .tyLe (.var 2) (.base .int)]

theorem chain_path (l r : TyTerm (Fin 3)) : Path (chain l r) 0 2 := by
  have first : Path (chain l r) 0 1 := .step (.refl (i := 0)) (by simp [chain])
  exact .step first (by simp [chain])

theorem chain_checked (l r : TyTerm (Fin 3)) : check (chain l r) = true := by
  apply (check_exact _).mpr
  exact ⟨.pair l r, .base .int, 0, 2, by simp [chain], by simp [chain],
    chain_path l r, CommonRoleStructuralConflicts.pair_scalar_conflict l r .int⟩

theorem chain_old_check_false (l r : TyTerm (Fin 3)) :
    CommonRoleStructuralConflicts.check (chain l r) = false := by
  rfl

theorem chain_no_model (l r : TyTerm (Fin 3)) (a : Fin 3 → Comp Common.model) :
    ¬ All Common.model a (chain l r) := checked_no_model _ (chain_checked l r) a

end Yulang.CommonRoleStructuralPaths
