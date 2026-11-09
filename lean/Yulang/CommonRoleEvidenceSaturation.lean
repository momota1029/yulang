import Yulang.CommonRoleDiagnosticEvidenceTransfer
import Yulang.FiniteHorn

/-! Exact finite scalar evidence closure along explicit reciprocal variable edges.
The capacity is the complete finite fact universe, not a language depth cutoff.
This does not decide arbitrary semantic consequences or change role selection. -/
namespace Yulang.CommonRoleEvidenceSaturation
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleDiagnosticEvidenceTransfer (edgeTest edgeTest_exact)

abbrev Fact (n : Nat) := Fin n × Inference.Base

def bases : List Inference.Base := [.int, .str, .bool, .unit]
def facts (n : Nat) : List (Fact n) :=
  (List.finRange n).flatMap fun i => bases.map fun b => (i,b)

theorem facts_complete (f : Fact n) : f ∈ facts n := by
  rcases f with ⟨i,b⟩
  cases b <;> simp [facts, bases]

theorem facts_length (n : Nat) : (facts n).length = n * 4 := by
  simp [facts, bases, List.length_flatMap, List.map_const', List.sum_replicate_nat]

def edge (s : State n) (i j : Fin n) : Bool :=
  s.atoms.any (edgeTest i j) && s.atoms.any (edgeTest j i)

def Linked (s : State n) (i j : Fin n) : Prop :=
  Atom.tyLe (.var i) (.var j) ∈ s.atoms ∧ Atom.tyLe (.var j) (.var i) ∈ s.atoms

theorem edge_exact (s : State n) (i j : Fin n) : edge s i j = true ↔ Linked s i j := by
  simp [edge, Linked, Bool.and_eq_true, List.any_eq_true, edgeTest_exact]

def seeds (s : State n) : List (Fact n) :=
  (List.finRange n).flatMap fun i =>
    (CommonRoleOrdinaryKnownness.candidates s.atoms i).map fun b => (i,b)

theorem seeds_exact (s : State n) (i : Fin n) (b : Inference.Base) :
    (i,b) ∈ seeds s ↔ Evidence s.atoms i b := by
  simp [seeds, CommonRoleOrdinaryKnownness.candidates_exact]

def seedRule (f : Fact n) : FiniteHorn.Rule (Fact n) := ⟨[],f⟩
def transferRule (i : Fin n) (f : Fact n) : FiniteHorn.Rule (Fact n) := ⟨[f],(i,f.2)⟩
def transfers (s : State n) (i : Fin n) : List (FiniteHorn.Rule (Fact n)) :=
  ((facts n).filter fun f => edge s i f.1).map (transferRule i)
def rules (s : State n) : List (FiniteHorn.Rule (Fact n)) :=
  (seeds s).map seedRule ++ (List.finRange n).flatMap (transfers s)
def saturate (s : State n) : List (Fact n) := FiniteHorn.saturate (rules s) (facts n)

inductive Derived (s : State n) : Fact n → Prop where
  | seed : Evidence s.atoms i b → Derived s (i,b)
  | transfer : Linked s i j → Derived s (j,b) → Derived s (i,b)

theorem saturate_capacity (s : State n) : (saturate s).length ≤ n * 4 := by
  rw [← facts_length]
  exact FiniteHorn.saturate_length_le _ _ facts_complete

theorem saturate_seed (s : State n) (h : Evidence s.atoms i b) :
    (i,b) ∈ saturate s := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  exact ⟨seedRule (i,b), List.mem_append_left _
    (List.mem_map.mpr ⟨(i,b),(seeds_exact ..).mpr h,rfl⟩),rfl,by simp [seedRule]⟩

theorem saturate_transfer (s : State n) (h : Linked s i j)
    (present : (j,b) ∈ saturate s) : (i,b) ∈ saturate s := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  refine ⟨transferRule i (j,b), List.mem_append_right _ ?_, rfl, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange _, List.mem_map.mpr ⟨(j,b), ?_, rfl⟩⟩
    exact List.mem_filter.mpr ⟨facts_complete _, (edge_exact ..).mpr h⟩
  · simpa [transferRule, saturate] using present

theorem rules_derived (s : State n) :
    ∀ rule ∈ rules s, FiniteHorn.Valid (Derived s) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with hs | ht
  · obtain ⟨⟨i,b⟩,h,rfl⟩ := List.mem_map.mp hs
    exact .seed ((seeds_exact ..).mp h)
  · obtain ⟨i,_,h⟩ := List.mem_flatMap.mp ht
    unfold transfers at h
    obtain ⟨⟨j,b⟩,filtered,same⟩ := List.mem_map.mp h
    subst rule
    exact .transfer ((edge_exact ..).mp (List.mem_filter.mp filtered).2)
      (premises (j,b) (by simp [transferRule]))

theorem saturate_exact (s : State n) (f : Fact n) :
    f ∈ saturate s ↔ Derived s f := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_derived s) f
  · intro h
    induction h with
    | seed h => exact saturate_seed s h
    | transfer h _ ih => exact saturate_transfer s h ih

/-- The executable engine has no fresh enabled fact after its internal capacity. -/
theorem saturate_stopped (s : State n) :
    FiniteHorn.firstFresh (rules s) (saturate s) (facts n) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro f _ h
  exact FiniteHorn.saturate_closed _ _ facts_complete f h

/-- Leastness against any independent closed set of scalar facts. -/
theorem saturate_least (s : State n) (P : Fact n → Prop)
    (seed : ∀ i b, Evidence s.atoms i b → P (i,b))
    (transfer : ∀ i j b, Linked s i j → P (j,b) → P (i,b)) :
    ∀ f ∈ saturate s, P f := by
  intro f h
  have d := (saturate_exact s f).mp h
  clear h
  induction d with
  | seed evidence => exact seed _ _ evidence
  | transfer linked _ ih => exact transfer _ _ _ linked ih

theorem derived_models (s : State n) (f : Fact n) (h : Derived s f)
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    Common.Equivalent (a f.1).1 (.base f.2) := by
  induction h with
  | seed h => exact CommonRoleOrdinaryKnownness.evidence_models _ _ _ h a models
  | transfer h _ ih => exact Common.equivalent_trans ⟨models _ h.1, models _ h.2⟩ ih

end Yulang.CommonRoleEvidenceSaturation
