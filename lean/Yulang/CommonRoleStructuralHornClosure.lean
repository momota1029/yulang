import Yulang.CommonRoleStructuralSaturationTrace

/-! A syntax-computed finite carrier for structural ordinary and supplied Horn
clauses together. Clauses can narrow models. This finite adapter is not general
role inference, source allocation, K2, or complete semantic subtyping. -/
namespace Yulang.CommonRoleStructuralHornClosure
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)
open CommonRoleFiniteStructuralClosure (compose carrier)
open CommonRoleStructuralCarrierCoverage
abbrev Clause (n : Nat) := FiniteHorn.Rule (Atom (Fin n))

def envelope (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :=
  seeds ++ clauses.flatMap (fun r => r.premises ++ [r.conclusion])
def carrierAtoms (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :=
  carrier (envelope seeds clauses)

/-- Independent mixed derivation: no cache, fuel, carrier, or solver. -/
inductive Derives (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) : Atom (Fin n) → Prop
  | seed (a) : a ∈ seeds → Derives seeds clauses a
  | split (a b) : Derives seeds clauses a → b ∈ CommonRoleStructuralDecomposition.atom a → Derives seeds clauses b
  | trans (a b c) : Derives seeds clauses a → Derives seeds clauses b → c ∈ compose a b → Derives seeds clauses c
  | clause (r) : r ∈ clauses → (∀ a ∈ r.premises, Derives seeds clauses a) → Derives seeds clauses r.conclusion

theorem derives_coverage {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {a}
    (h : Derives seeds clauses a) : a ∈ carrierAtoms seeds clauses := by
  induction h with
  | seed a member => exact seed_coverage _ _ (List.mem_append_left _ member)
  | split a b _ member ih => exact split_coverage _ _ _ ih member
  | trans a b c _ _ member iha ihb => exact trans_coverage _ _ _ _ iha ihb member
  | clause r member _ _ =>
    exact seed_coverage _ _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨r,member,List.mem_append_right _ (by simp)⟩))

def splitRules (u : List (Atom (Fin n))) : List (Clause n) :=
  u.flatMap fun a => (CommonRoleStructuralDecomposition.atom a).map fun b => ⟨[a],b⟩
def transRules (u : List (Atom (Fin n))) : List (Clause n) :=
  u.flatMap fun a => u.flatMap fun b => (compose a b).map fun c => ⟨[a,b],c⟩
def rules (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) : List (Clause n) :=
  (seeds.map fun a => ⟨[],a⟩) ++ splitRules (carrierAtoms seeds clauses) ++
    transRules (carrierAtoms seeds clauses) ++ clauses

def saturate (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :=
  FiniteHorn.saturate (rules seeds clauses) (carrierAtoms seeds clauses)

private theorem rules_valid (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    ∀ r ∈ rules seeds clauses, FiniteHorn.Valid (Derives seeds clauses) r := by
  intro r member premises
  rcases List.mem_append.mp member with ordinary | role
  · rcases List.mem_append.mp ordinary with early | trans
    · rcases List.mem_append.mp early with seed | split
      · obtain ⟨a,seedMem,rfl⟩ := List.mem_map.mp seed
        exact .seed a seedMem
      · obtain ⟨a,_,member⟩ := List.mem_flatMap.mp split
        obtain ⟨b,splitMem,rfl⟩ := List.mem_map.mp member
        exact .split a b (premises _ (by simp)) splitMem
    · obtain ⟨a,_,member⟩ := List.mem_flatMap.mp trans
      obtain ⟨b,_,member⟩ := List.mem_flatMap.mp member
      obtain ⟨c,transMem,rfl⟩ := List.mem_map.mp member
      exact .trans a b c (premises _ (by simp)) (premises _ (by simp)) transMem
  · exact .clause r role premises

/-- Relative finite closure needs coverage of the reachable cache, not a finite
carrierAtoms for the entire ambient atom type. -/
theorem run_closed [DecidableEq α] (rs : List (FiniteHorn.Rule α)) (u : List α)
    (capacity : Nat) (seen : List α) (distinct : seen.Nodup)
    (covered : ∀ a ∈ seen, a ∈ u) (enough : u.length ≤ seen.length + capacity) :
    ∀ a ∈ u, FiniteHorn.Enabled rs (FiniteHorn.run rs u capacity seen) a →
      a ∈ FiniteHorn.run rs u capacity seen := by
  induction capacity generalizing seen with
  | zero =>
    intro a member _
    by_cases present : a ∈ seen
    · exact present
    · have distinct' := List.nodup_cons.mpr ⟨present,distinct⟩
      have bound := distinct'.length_le_of_subset (l₂ := u) (by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact member
        · exact covered b hb)
      simp only [List.length_cons,Nat.add_zero] at bound enough
      omega
  | succ capacity ih =>
    simp only [FiniteHorn.run]
    cases found : FiniteHorn.firstFresh rs seen u with
    | none => exact (FiniteHorn.firstFresh_none_iff ..).mp found
    | some a =>
      have chosen := FiniteHorn.firstFresh_some rs seen u found
      apply ih (a :: seen) (List.nodup_cons.mpr ⟨chosen.2.1,distinct⟩)
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact chosen.1
        · exact covered b hb
      · simp only [List.length_cons]; omega

theorem saturate_closed (seeds : List (Atom (Fin n))) (clauses : List (Clause n))
    (a : Atom (Fin n)) (covered : a ∈ carrierAtoms seeds clauses)
    (enabled : FiniteHorn.Enabled (rules seeds clauses) (saturate seeds clauses) a) :
    a ∈ saturate seeds clauses :=
  run_closed _ _ _ [] (by simp) (by simp) (by simp) a covered enabled

/-- Exactness for arbitrary finite clauses plus structural seed/split/trans.
No externally supplied carrier-coverage premise or derivation bound remains. -/
theorem saturate_exact (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (a) :
    a ∈ saturate seeds clauses ↔ Derives seeds clauses a := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_valid seeds clauses) a
  · intro derived
    induction derived with
    | seed a member =>
      apply saturate_closed _ _ _ (derives_coverage (.seed a member))
      refine ⟨⟨[],a⟩,?_,rfl,by simp⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨a,member,rfl⟩)))
    | split a b derived member ih =>
      apply saturate_closed _ _ _ (derives_coverage (.split a b derived member))
      refine ⟨⟨[a],b⟩,?_,rfl,by simpa using ih⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨a,derives_coverage derived,List.mem_map.mpr ⟨b,member,rfl⟩⟩)))
    | trans a b c da db member iha ihb =>
      apply saturate_closed _ _ _ (derives_coverage (.trans a b c da db member))
      refine ⟨⟨[a,b],c⟩,?_,rfl,by simpa using And.intro iha ihb⟩
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨a,derives_coverage da,List.mem_flatMap.mpr
          ⟨b,derives_coverage db,List.mem_map.mpr ⟨c,member,rfl⟩⟩⟩))
    | clause r member derived ih =>
      apply saturate_closed _ _ _ (derives_coverage (.clause r member derived))
      exact ⟨r,List.mem_append_right _ member,rfl,ih⟩

theorem stopped (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    FiniteHorn.firstFresh (rules seeds clauses) (saturate seeds clauses) (carrierAtoms seeds clauses) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  exact saturate_closed seeds clauses

theorem saturate_nodup (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (saturate seeds clauses).Nodup := FiniteHorn.saturate_nodup ..

theorem saturate_bounded (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (saturate seeds clauses).length ≤ (carrierAtoms seeds clauses).length :=
  (saturate_nodup seeds clauses).length_le_of_subset
    (fun a h => derives_coverage ((saturate_exact seeds clauses a).mp h))

/-- Exact all-model semantics. Activated clauses can narrow the initial models;
ordinary implications themselves remain model preserving. -/
theorem models_exact (seeds : List (Atom (Fin n))) (clauses : List (Clause n))
    (v : Fin n → Comp Common.model) :
    All Common.model v (saturate seeds clauses) ↔ All Common.model v seeds ∧
      ∀ r ∈ clauses, (∀ a ∈ r.premises, Derives seeds clauses a) → r.conclusion.Holds Common.model v := by
  constructor
  · intro models
    exact ⟨fun a h => models a ((saturate_exact ..).mpr (.seed a h)),
      fun r member premises => models _ ((saturate_exact ..).mpr (.clause r member premises))⟩
  · rintro ⟨initial,clausesValid⟩ a member
    have derived := (saturate_exact seeds clauses a).mp member
    clear member
    induction derived with
    | seed a member => exact initial a member
    | split a b _ member ih => exact (CommonRoleStructuralDecomposition.atom_exact a v).mpr ih b member
    | trans a b c _ _ member iha ihb => exact CommonRoleFiniteStructuralClosure.compose_sound a b v iha ihb c member
    | clause r member premises _ => exact clausesValid r member premises

/-- Independent least closure, useful for permutation and fixed-point proofs. -/
theorem derives_cut {seeds more : List (Atom (Fin n))} {clauses : List (Clause n)} {a}
    (initial : ∀ b ∈ more, Derives seeds clauses b) (h : Derives more clauses a) :
    Derives seeds clauses a := by
  induction h with
  | seed b member => exact initial b member
  | split b c _ member ih => exact .split b c ih member
  | trans b c d _ _ member ihb ihc => exact .trans b c d ihb ihc member
  | clause r member _ ih => exact .clause r member ih

theorem saturate_idempotent (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (a) :
    a ∈ saturate (saturate seeds clauses) clauses ↔ a ∈ saturate seeds clauses := by
  rw [saturate_exact]
  constructor
  · intro h
    exact (saturate_exact ..).mpr (derives_cut (fun b hb => (saturate_exact ..).mp hb) h)
  · intro h; exact .seed a h

/-- The causal sequence is computed internally and consists of fresh atoms,
not just fresh indices. It cannot stop on a temporary materialization plateau. -/
def generated (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :=
  CommonRoleStructuralSaturationTrace.discoveries (rules seeds clauses) (carrierAtoms seeds clauses)
    (carrierAtoms seeds clauses).length []

theorem generated_reverse (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (generated seeds clauses).reverse = saturate seeds clauses := by
  symm
  simpa [generated,saturate,FiniteHorn.saturate] using
    CommonRoleStructuralSaturationTrace.discoveries_result (rules seeds clauses)
      (carrierAtoms seeds clauses) (carrierAtoms seeds clauses).length []

theorem generated_execution_complete (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    CommonRoleStructuralSaturationTrace.Execution (rules seeds clauses) [] (generated seeds clauses) ∧
      FiniteHorn.firstFresh (rules seeds clauses) (generated seeds clauses).reverse (carrierAtoms seeds clauses) = none := by
  exact ⟨CommonRoleStructuralSaturationTrace.discoveries_execution ..,
    by rw [generated_reverse]; exact stopped ..⟩

end Yulang.CommonRoleStructuralHornClosure
