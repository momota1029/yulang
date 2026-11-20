import Yulang.GeneralGeneratedDictionaryRankCheck299

namespace Yulang.GeneralGeneratedDictionaryRankExists299
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryMinFuel299
open GeneralGeneratedDictionaryRankCheck299

theorem found_at_cap (read : Read) (i cap : Nat)
    (hit : ∃ d, run read cap i = some d) : ∃ k, earliest read i cap = some k := by
  cases eq : earliest read i cap with
  | some k => exact ⟨k,rfl⟩
  | none =>
    obtain ⟨_,d⟩ := hit
    have absent := earliest_none read i cap eq cap (Nat.le_refl _)
    rw [absent] at d
    cases d

theorem all_tested_bound (read : Read) (domain : List Nat) (closed : Closed read)
    (covered : ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i) :
    ∃ cap, check read domain cap = true := by
  have each : ∀ i ∈ domain, ∃ n dc, run read n i = some dc := by
    intro i mem
    obtain ⟨⟨row,hit⟩,acc⟩ := covered i mem
    exact accessible_success read closed i acc row hit
  obtain ⟨cap,passed⟩ := common_fuel read domain each
  refine ⟨cap,List.all_eq_true.mpr ?_⟩
  intro i mem
  obtain ⟨⟨row,hit⟩,_⟩ := covered i mem
  obtain ⟨k,when⟩ := found_at_cap read i cap (passed i mem)
  simp [hit,when]

theorem finite_exact (read : Read) (domain : List Nat) (closed : Closed read) :
    (∃ cap, check read domain cap = true) ↔
      ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i := by
  constructor
  · rintro ⟨cap,pass⟩ i mem
    obtain ⟨row,⟨k,when⟩⟩ := checked_at read domain cap pass mem
    obtain ⟨d,hit⟩ := (earliest_some read i cap k when).2.1
    exact ⟨row,success_accessible read k i d hit⟩
  · exact all_tested_bound read domain closed

theorem ranked_of_finite_accessibility (read : Read) (domain : List Nat)
    (known : Known read domain) (closed : Closed read)
    (covered : ∀ i ∈ domain, (∃ row, read i = some row) ∧ Acc (Edge read) i) :
    ∃ cap, check read domain cap = true ∧ Ranked read (inferredRank read cap) := by
  obtain ⟨cap,passed⟩ := all_tested_bound read domain closed covered
  exact ⟨cap,passed,checked_ranked read domain cap known passed⟩

end Yulang.GeneralGeneratedDictionaryRankExists299
