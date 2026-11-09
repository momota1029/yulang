import Yulang.CommonRoleOrdinaryKnownness
import Yulang.FiniteHorn

/-! Dynamic receiver feedback for a finite list of actual Index(box str) requests.
The source graph is supplied; this is a str-only fragment, not general roles.
Facts trigger declaration evaluation only after explicit scalar evidence exists. -/
namespace Yulang.CommonRoleDynamicIndexClosure
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleCandidateStateFrontier (extend equality)

abbrev Edges (n : Nat) := List (Fin n × Fin n)
def seeds (s : State n) : List (Fin n) :=
  (List.finRange n).filter fun i =>
    (CommonRoleOrdinaryKnownness.candidates s.atoms i).contains .str

theorem seeds_exact (s : State n) (i : Fin n) :
    i ∈ seeds s ↔ Evidence s.atoms i .str := by
  simp [seeds, CommonRoleOrdinaryKnownness.candidates_exact]

def rules (s : State n) (edges : Edges n) : List (FiniteHorn.Rule (Fin n)) :=
  (seeds s).map (fun i => ⟨[], i⟩) ++ edges.map (fun e => ⟨[e.1], e.2⟩)
def saturate (s : State n) (edges : Edges n) : List (Fin n) :=
  FiniteHorn.saturate (rules s edges) (List.finRange n)

inductive Derived (s : State n) (edges : Edges n) : Fin n → Prop where
  | seed : Evidence s.atoms i .str → Derived s edges i
  | index : (i,j) ∈ edges → Derived s edges i → Derived s edges j

theorem seed_present (s : State n) (edges : Edges n) (h : Evidence s.atoms i .str) :
    i ∈ saturate s edges := by
  apply FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _)
  exact ⟨⟨[],i⟩,List.mem_append_left _ (List.mem_map.mpr
    ⟨i,(seeds_exact ..).mpr h,rfl⟩),rfl,by simp⟩

theorem index_present (s : State n) (edges : Edges n) (edge : (i,j) ∈ edges)
    (hi : i ∈ saturate s edges) : j ∈ saturate s edges := by
  apply FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _)
  exact ⟨⟨[i],j⟩,List.mem_append_right _ (List.mem_map.mpr ⟨(i,j),edge,rfl⟩),
    rfl,by simpa [saturate] using hi⟩

theorem saturate_exact (s : State n) (edges : Edges n) (i : Fin n) :
    i ∈ saturate s edges ↔ Derived s edges i := by
  constructor
  · apply FiniteHorn.saturate_preserves _ _ (Derived s edges)
    intro r hr hp
    rcases List.mem_append.mp hr with hs | he
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
      exact .seed ((seeds_exact ..).mp hj)
    · obtain ⟨⟨j,k⟩,hj,rfl⟩ := List.mem_map.mp he
      exact .index hj (hp j (by simp))
  · intro h
    induction h with
    | seed h => exact seed_present s edges h
    | index h _ ih => exact index_present s edges h ih

theorem stopped (s : State n) (edges : Edges n) :
    FiniteHorn.firstFresh (rules s edges) (saturate s edges) (List.finRange n) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro i _ h
  exact FiniteHorn.saturate_closed _ _ (fun _ => List.mem_finRange _) i h

theorem capacity (s : State n) (edges : Edges n) : (saturate s edges).length ≤ n := by
  simpa [saturate] using FiniteHorn.saturate_length_le (rules s edges) (List.finRange n)
    (fun _ => List.mem_finRange _)

theorem least (s : State n) (edges : Edges n) (P : Fin n → Prop)
    (seed : ∀ i, Evidence s.atoms i .str → P i)
    (step : ∀ i j, (i,j) ∈ edges → P i → P j) : ∀ i ∈ saturate s edges, P i := by
  intro i hi
  have h := (saturate_exact s edges i).mp hi
  clear hi
  induction h with
  | seed h => exact seed _ h
  | index h _ ih => exact step _ _ h ih

def record (s : State n) : List (Fin n) → State n
  | [] => s
  | i :: rest => extend (record s rest) i .str

theorem record_atoms (s : State n) (xs : List (Fin n)) :
    (record s xs).atoms = s.atoms ++ (xs.reverse.flatMap fun i => equality i .str) := by
  induction xs with
  | nil => simp [record]
  | cons i xs ih => simp [record,extend,ih,List.flatMap_append,List.append_assoc]

theorem record_models (s : State n) (xs : List (Fin n)) (a : Fin n → Comp Common.model) :
    All Common.model a (record s xs).atoms ↔
    All Common.model a s.atoms ∧ ∀ i ∈ xs, Common.Equivalent (a i).1 (.base .str) := by
  induction xs with
  | nil => simp [record]
  | cons i xs ih =>
    rw [record,CommonRoleCandidateStateFrontier.extend_exact,ih]
    simp only [List.mem_cons,forall_eq_or_imp]
    constructor
    · rintro ⟨⟨ha,hxs⟩,hi⟩; exact ⟨ha,hi,hxs⟩
    · rintro ⟨ha,hi,hxs⟩; exact ⟨⟨ha,hxs⟩,hi⟩

theorem record_evidence (s : State n) (xs : List (Fin n)) (i : Fin n) (hi : i ∈ xs) :
    Evidence (record s xs).atoms i .str := by
  rw [CommonRoleOrdinaryKnownness.Evidence, record_atoms]
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatMap.mpr
  all_goals exact ⟨i,by simpa using hi,by simp [equality]⟩

def output (s : State n) (edges : Edges n) : State n := record s (saturate s edges)

/-- The model family includes every reachable declaration equation, not equations
for unreachable receivers. It is not claimed to preserve all seed models. -/
theorem output_models (s : State n) (edges : Edges n) (a : Fin n → Comp Common.model) :
    All Common.model a (output s edges).atoms ↔
    All Common.model a s.atoms ∧ ∀ i, Derived s edges i →
      Common.Equivalent (a i).1 (.base .str) := by
  simp only [output,record_models,saturate_exact]

theorem detects_recorded (s : State n) (xs : List (Fin n)) (i : Fin n) (hi : i ∈ xs)
    (a : Fin n → Comp Common.model) (hm : All Common.model a (record s xs).atoms) :
    CommonRoleOrdinaryKnownness.detect (record s xs).atoms i = some .str := by
  have he := record_evidence s xs i hi
  obtain ⟨b,hb⟩ := (CommonRoleOrdinaryKnownness.detect_exists _ i).mpr ⟨.str,he⟩
  have eq := CommonRoleOrdinaryKnownness.evidence_unique _ i a hm b .str
    (CommonRoleOrdinaryKnownness.detect_evidence _ i b hb) he
  simpa [eq] using hb

/-- Every enabled receiver is passed to the existing checked declaration engine.
Ordinary consistency is explicit because contradictory evidence has no unique read. -/
theorem actual_index_step (s : State n) (edges : Edges n) (i j : Fin n)
    (hi : Derived s edges i) (a : Fin n → Comp Common.model)
    (hm : All Common.model a (output s edges).atoms) :
    CommonRoleOrdinaryKnownness.produceIndex (output s edges) i j =
      some (extend (output s edges) j .str) := by
  apply CommonRoleOrdinaryKnownness.index_from_detected_str
  exact detects_recorded s (saturate s edges) i ((saturate_exact ..).mpr hi) a hm

/-- Re-running any enabled source edge at the final state adds no new models. -/
theorem actual_step_models_fixed (s : State n) (edges : Edges n) (i j : Fin n)
    (edge : (i,j) ∈ edges) (hi : Derived s edges i) (a : Fin n → Comp Common.model) :
    All Common.model a (extend (output s edges) j .str).atoms ↔
      All Common.model a (output s edges).atoms := by
  rw [CommonRoleCandidateStateFrontier.extend_exact]
  constructor
  · exact And.left
  · intro hm
    exact ⟨hm,((output_models s edges a).mp hm).2 j (.index edge hi)⟩

/-- Source scheduling trace. Seeds record an existing equation; index steps
require the receiver to have been recorded earlier, including through feedback. -/
inductive Trace (s : State n) (edges : Edges n) : List (Fin n) → Prop where
  | nil : Trace s edges []
  | seed : Trace s edges xs → Evidence s.atoms i .str → Trace s edges (i :: xs)
  | index : Trace s edges xs → (i,j) ∈ edges → i ∈ xs → Trace s edges (j :: xs)

theorem trace_derived (s : State n) (edges : Edges n) (xs : List (Fin n))
    (h : Trace s edges xs) : ∀ i ∈ xs, Derived s edges i := by
  induction h with
  | nil => simp
  | seed _ he ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact .seed he
    · exact ih _ hj
  | index _ he hi ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact .index he (ih _ hi)
    · exact ih _ hj

theorem run_trace (s : State n) (edges : Edges n) (fuel : Nat)
    (xs : List (Fin n)) (h : Trace s edges xs) :
    Trace s edges (FiniteHorn.run (rules s edges) (List.finRange n) fuel xs) := by
  induction fuel generalizing xs with
  | zero => exact h
  | succ fuel ih =>
    simp only [FiniteHorn.run]
    cases found : FiniteHorn.firstFresh (rules s edges) xs (List.finRange n) with
    | none => exact h
    | some i =>
      apply ih
      obtain ⟨_,_,r,hr,eq,hp⟩ := FiniteHorn.firstFresh_some _ _ _ found
      rcases List.mem_append.mp hr with hs | he
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
        cases eq
        exact .seed h ((seeds_exact ..).mp hj)
      · obtain ⟨⟨j,k⟩,hj,rfl⟩ := List.mem_map.mp he
        cases eq
        exact .index h hj (hp j (by simp))

theorem saturate_trace (s : State n) (edges : Edges n) : Trace s edges (saturate s edges) :=
  run_trace s edges _ [] .nil

/-- Every recorded schedule is interpreted by the existing producer, not a
replacement equation generator. Seed moves only duplicate existing facts. -/
inductive Executed (s : State n) (edges : Edges n) : List (Fin n) → Prop where
  | nil : Executed s edges []
  | seed : Executed s edges xs → Evidence s.atoms i .str → Executed s edges (i :: xs)
  | index : Executed s edges xs → (i,j) ∈ edges →
      CommonRoleOrdinaryKnownness.produceIndex (record s xs) i j =
        some (record s (j :: xs)) → Executed s edges (j :: xs)

/-- Consistency of the complete output suffices for every intermediate receiver
read. This theorem neither proves consistency nor turns absence into rejection. -/
theorem trace_executes (s : State n) (edges : Edges n) (xs : List (Fin n))
    (h : Trace s edges xs) (a : Fin n → Comp Common.model)
    (hm : All Common.model a (output s edges).atoms) : Executed s edges xs := by
  have all := (output_models s edges a).mp hm
  induction h with
  | nil => exact .nil
  | seed _ he ih => exact .seed ih he
  | @index xs i j hx he hi ih =>
    apply Executed.index ih he
    apply CommonRoleOrdinaryKnownness.index_from_detected_str
    apply detects_recorded s xs i hi a
    exact (record_models s xs a).mpr ⟨all.1,fun k hk => all.2 k
      (trace_derived s edges xs hx k hk)⟩

theorem saturate_executes (s : State n) (edges : Edges n)
    (a : Fin n → Comp Common.model) (hm : All Common.model a (output s edges).atoms) :
    Executed s edges (saturate s edges) :=
  trace_executes s edges _ (saturate_trace s edges) a hm

/-- Recording string facts introduces no other string evidence. -/
theorem record_evidence_exact (s : State n) (xs : List (Fin n)) (i : Fin n) :
    Evidence (record s xs).atoms i .str ↔ Evidence s.atoms i .str ∨ i ∈ xs := by
  induction xs with
  | nil => simp [record]
  | cons j xs ih =>
    by_cases h : i = j
    · subst i
      simp [Evidence,record,extend,equality]
    · simpa [Evidence,record,extend,equality,h] using ih

/-- Re-saturating the output has exactly the same membership, even without a
model assumption. List order and duplicated state atoms are not identified. -/
theorem saturate_output_fixed (s : State n) (edges : Edges n) (i : Fin n) :
    i ∈ saturate (output s edges) edges ↔ i ∈ saturate s edges := by
  constructor
  · intro hi
    apply least (output s edges) edges (fun j => j ∈ saturate s edges) ?_ ?_ i hi
    · intro j hj
      rcases (record_evidence_exact s (saturate s edges) j).mp hj with h | h
      · exact seed_present s edges h
      · exact h
    · intro j k h hj
      exact index_present s edges h hj
  · intro hi
    exact seed_present (output s edges) edges (record_evidence s _ i hi)

end Yulang.CommonRoleDynamicIndexClosure
