import Yulang.GeneralWhereVersionLeafHead317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 37000000
namespace Yulang.GeneralWhereVersionLeafFresh317
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (registry leaf source)
open GeneralLiveCompoundPost316 (raw)
open GeneralWhereVersionCase317 (site occ lower upper descriptor expr)
open GeneralWhereVersionBase317 (loSlot hiSlot injectOld source_old source_lo source_hi)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionCommit317 (terminal_outputs new_snapshot)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionLeafHead317 (packet plan located report_exact binding head)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalState (sources Known)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (otherChild)

theorem finite_sources {n : Nat} (inside : n ∈ sources snap) :
    n ∈ sources raw ∨ n = lower ∨ n = upper := by
  have from_slot (i : Fin 10) : GeneralWhereVersionBase317.source i ∈ sources raw ∨
      GeneralWhereVersionBase317.source i = lower ∨ GeneralWhereVersionBase317.source i = upper := by
    refine Fin.addCases (m := 8) (n := 2) (fun j => ?_) (fun j => ?_) i
    · rw [show GeneralWhereVersionBase317.source (j.castAdd 2) = _ from source_old j]
      exact Or.inl (GeneralNominalAllocationSupport.slot_source raw j)
    · rcases GeneralWhereVersionBase317.new_cases j with rfl|rfl
      · exact Or.inr (Or.inl source_lo)
      · exact Or.inr (Or.inr source_hi)
  simp only [sources,List.mem_append] at inside
  rcases inside with ((a|b)|r)|ordinary
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp a
    exact from_slot i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp b
    exact from_slot i
  · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ r))
  · exact Or.inl (List.mem_append_right _ ordinary)

theorem owner_eq : occ.identity = GeneralLiveCompoundChildSite316.child.identity := by
  have h := GeneralWhereVersionCompiler317.child_owner rootPlan otherChild GeneralLiveCompoundChildSite316.signature
  change occ.identity = _ at h
  change occ.identity = _
  exact h.trans (by
    change (GeneralNominalVersionedFrame231.childSite
      (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLiveCompoundCurrentRoot316.plan)
      otherChild GeneralLiveCompoundChildSite316.signature).occurrence.identity = _
    rw [GeneralNominalVersionedTransport231.childSite_eq,GeneralLiveCompoundPostRootHead316.child_site])

theorem old_reservation : ∀ k ∈ GeneralNominalVersionedAllocation231.keys registry occ.identity [(0,2,2)],
    GeneralNominalIdentities.source raw.seed k ∉ sources raw ∨ k ∈ raw.allocated := by
  rw [owner_eq]
  decide +kernel

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry occ.identity packet.bindings := by
  intro k member collision
  have low : k.2.2.1 ≤ 6 := by
    apply GeneralVersionedInstallDomain313.reserve_purpose packet
    exact List.mem_map.mpr ⟨k,member,rfl⟩
  rcases finite_sources collision with old|eq|eq
  · rw [binding] at member
    exact (old_reservation k member).resolve_left (fun no => no old)
  · exact False.elim (GeneralVersionedHighOrigins315.distinct
      (b := GeneralVersionedEndpointAddress315.key rootPlan .lower otherChild.id 0 expr)
      (by change k.2.2.1 ≠ 10; omega) snap.seed eq)
  · exact False.elim (GeneralVersionedHighOrigins315.distinct
      (b := GeneralVersionedEndpointAddress315.key rootPlan .upper otherChild.id 0 expr)
      (by change k.2.2.1 ≠ 11; omega) snap.seed eq)

theorem known : ¬ GeneralNominalState.RootPending snap (inputs occ).demand := by
  rintro ⟨i,unknown⟩
  have iz : i = 0 := Fin.ext (by
    have p : i.val < 1 := i.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p))
  subst i
  apply unknown
  refine ⟨loSlot,?_,Or.inl ?_⟩
  · change GeneralWhereVersionBase317.source loSlot = (occ.demand.arguments 0).1
    rw [descriptor]; exact source_lo
  · change (GeneralWhereVersionSnapshot317.viewHeads loSlot).node ≠ .unresolved
    decide +kernel

theorem prepared (m : GeneralNominalCommonBridge.Assignment) (valid : ParentHolds m) :
    Prepared registry context occ leaf := by
  refine ⟨source.metadata,⟨?_,by intro out absent; cases absent⟩,
    [(loSlot,hiSlot)],located,?_,?_,m,head m valid⟩
  · intro i
    have iz : i = 0 := Fin.ext (by
      have p : i.val < 1 := i.isLt
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p))
    subst i
    change ((inputs occ).demand.arguments 0).1 ∈ sources snap ∧ ((inputs occ).demand.arguments 0).2 ∈ sources snap
    change (occ.demand.arguments 0).1 ∈ sources snap ∧ (occ.demand.arguments 0).2 ∈ sources snap
    rw [descriptor]
    exact ⟨source_lo ▸ GeneralNominalAllocationSupport.slot_source snap loSlot,
      source_hi ▸ GeneralNominalAllocationSupport.slot_source snap hiSlot⟩
  · exact fresh
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralWhereVersionLeafFresh317
