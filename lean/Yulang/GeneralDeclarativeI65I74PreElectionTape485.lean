import Yulang.GeneralDeclarativeI65I74ExactCandidateTape485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)

/-- Keep every successful hit at its physical registry ordinal. This
does not choose a diagnostic occurrence among several hits. -/
def positiveOrdinals485 (bits : List (Nat × Bool)) : List Nat :=
  (bits.filter Prod.snd).map Prod.fst

inductive PreElection485 where
  | recursive (ordinals : List Nat)
  | allSafe (ordinals : List Nat)
  deriving DecidableEq, Repr

def gate485 (bits : List (Nat × Bool)) : PreElection485 :=
  match positiveOrdinals485 bits with
  | [] => .allSafe (bits.map Prod.fst)
  | i::is => .recursive (i::is)

def beforeElection485 (p : FullProblem) (check : CandidateCheck Wire)
    (wires : List (Nat × Wire)) : Option PreElection485 :=
  (readTape485 p check wires).map gate485

theorem positive_ordinal_is_a_real_positive_local_tape_slot485
    (bits : List (Nat × Bool)) (ord : Nat) :
    ord ∈ positiveOrdinals485 bits ↔ (ord,true) ∈ bits := by
  simp only [positiveOrdinals485,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨⟨atSource,b⟩,⟨member,yes⟩,rfl⟩
    have trueBit : b = true := yes
    subst b
    exact member
  · intro member
    exact ⟨(ord,true),⟨member,rfl⟩,rfl⟩

theorem every_real_positive_is_kept_before_any_election485
    (bits : List (Nat × Bool)) (ord : Nat) (positive : (ord,true) ∈ bits) :
    gate485 bits = .recursive (positiveOrdinals485 bits) ∧
    ord ∈ positiveOrdinals485 bits := by
  have reported := (positive_ordinal_is_a_real_positive_local_tape_slot485 bits ord).mpr positive
  refine ⟨?_,reported⟩
  cases h : positiveOrdinals485 bits with
  | nil => simp [h] at reported
  | cons i is => simp [gate485,h]

theorem safe_before_election_means_every_exact_slot_has_negative_result485
    (bits : List (Nat × Bool)) (ords : List Nat) :
    gate485 bits = .allSafe ords ↔
      ords = bits.map Prod.fst ∧ ∀ i, (i,true) ∉ bits := by
  cases positives : positiveOrdinals485 bits with
  | nil =>
    unfold gate485
    rw [positives]
    constructor
    · intro same
      have ok : bits.map Prod.fst = ords := PreElection485.allSafe.inj same
      exact ⟨ok.symm,fun i mem => by
        have present := (positive_ordinal_is_a_real_positive_local_tape_slot485 bits i).mpr mem
        simp [positives] at present⟩
    · rintro ⟨rfl,_⟩
      rfl
  | cons i is =>
    unfold gate485
    rw [positives]
    constructor
    · intro h
      cases h
    · intro safe
      have member : i ∈ positiveOrdinals485 bits := by simp [positives]
      exact False.elim (safe.2 i ((positive_ordinal_is_a_real_positive_local_tape_slot485 bits i).mp member))

theorem ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485
    (p : FullProblem) (check : CandidateCheck Wire) (meaning : CandidateLocal Wire)
    (localExact : ∀ ord d wire bit, check ord d wire = some bit ↔ meaning ord d wire bit)
    (wires : List (Nat × Wire)) (out : PreElection485) :
    beforeElection485 p check wires = some out ↔
      ∃ bits, ExactTape485 p meaning (List.range (visible485 p).length) wires bits ∧ gate485 bits = out := by
  unfold beforeElection485
  cases exact : readTape485 p check wires with
  | none =>
    constructor
    · simp
    · rintro ⟨bits,source,_⟩
      rw [(read_tape_reflects_the_actual_entire_visible_order485 p check meaning localExact wires bits).mpr source] at exact
      cases exact
  | some bits =>
    constructor
    · intro h
      exact ⟨bits,
        (read_tape_reflects_the_actual_entire_visible_order485 p check meaning localExact wires bits).mp exact,
        Option.some.inj h⟩
    · rintro ⟨other,source,rfl⟩
      have ran := (read_tape_reflects_the_actual_entire_visible_order485 p check meaning localExact wires other).mpr source
      cases Option.some.inj (exact.symm.trans ran)
      rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
