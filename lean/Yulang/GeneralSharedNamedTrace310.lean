import Yulang.GeneralSharedNamedNoHistory310
import Yulang.GeneralCommittedReadAddress309
import Yulang.GeneralSelectedReadEvidence309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 16500000
namespace Yulang.GeneralSharedNamedTrace310
open GeneralSharedNamedSource310 (root registry compiled checked)
open GeneralSharedNamedPlan310 (z)
open GeneralSharedNamedNodes310 (Node plan focus key links child_list current_frame)
open GeneralSharedNamedSelection310 (safe unique no_merged)
open GeneralSharedNamedCompiler310 (read decode row encode lookup_row projected_children decode_encode)
open GeneralSharedNamedMerge310 (merged reached inhabited)
open GeneralSharedNamedEvidence310 (payload)
open GeneralSharedNamedNoHistory310 (committed_without_packet)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralSelectedReadEvidence309 (SelectedRead)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralCommittedReadTrace309 (Trace)
open GeneralCommittedReadAddress309 (cursor subtree subtrace here)
open GeneralNominalCenters (Plan)
open GeneralDictionaryReadback (Payload)

theorem root_committed : Committed merged (plan .parent) := by
  have same := GeneralSharedNamedHistoryReplay310.composed_parent
  rw [show plan .parent = GeneralSharedNamedCurrent310.parent from rfl,same]
  exact GeneralNominalVersionedMixedReplay237.recorded_committed _ _ _ reached List.mem_cons_self
    (same ▸ GeneralSharedNamedCurrent310.current_parent.context_eq)

theorem committed (n : Node) : Committed merged (plan n) := by
  cases n
  · exact root_committed
  · exact committed_without_packet .low
  · exact committed_without_packet .high

theorem verified_rows : SelectedRead registry merged read decode := by
  intro i e hit
  obtain ⟨n,rfl,rfl⟩ := lookup_row i e hit
  rw [decode_encode,projected_children]
  exact ⟨⟨plan n,current_frame n,child_list n,committed n⟩,safe n,unique n,no_merged n⟩

theorem validation (fuel : Nat) (d : Payload) :
    validate read fuel 0 d = .ok () ↔ 2 ≤ fuel ∧ d = payload :=
  (GeneralOrderedDictionaryCheck309.exact read fuel 0 d).trans
    (GeneralSharedNamedCompiler310.root_code_exact fuel d)

theorem sound (fuel : Nat) (d : Payload) (accepted : validate read fuel 0 d = .ok ()) :
    B4TargetV8.Classify (boundary roles) registry merged root (.selected d) ∧
    ∀ m, Models merged m → Trace registry merged root m read decode 0 d ∧
      (boundary roles).Evidence registry merged m root d :=
  GeneralSelectedReadEvidence309.selected_checker ⟨rfl,checked⟩ reached read decode verified_rows ⟨_,inhabited⟩
    fuel 0 d .root accepted

theorem exact_trace (m : Assignment) (valid : Models merged m) :
    Trace registry merged root m read decode 0 payload :=
  ((sound 2 payload ((validation _ _).mpr ⟨Nat.le_refl _,rfl⟩)).2 m valid).1

theorem root_table : read 0 = some ⟨1,[1,2]⟩ := by
  change some (row .parent) = _
  rw [GeneralSharedNamedCompiler310.row_exact]
  rfl

theorem left_address : cursor read 0 [0] = some 1 ∧ subtree payload [0] = some (.node 2 []) :=
  ⟨by simp [cursor,root_table],rfl⟩

theorem right_address : cursor read 0 [1] = some 2 ∧ subtree payload [1] = some (.node 2 []) :=
  ⟨by simp [cursor,root_table],rfl⟩

theorem distinct_occurrence : decode 1 ≠ decode 2 := by
  intro same
  exact GeneralSharedNamedEvidence310.siblings_different (congrArg GeneralSourceDictionaries.Occurrence.identity same)

theorem not_deduplicated :
    validate read 2 0 (.node 1 [.node 2 []]) = .error (.wrongArity 0 2 1) := by
  simp [validate,root_table]

/-- Same payload keys and aliased inputs do not erase either source
    occurrence. Each exact ordinal still exports its own output witness. -/
theorem both_addresses (m : Assignment) (valid : Models merged m) :
    (∃ p : Plan roles, Certificate compiled merged.core m (focus .low) 2 [] p ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness p m ⟨1,z⟩) ∧
    (∃ p : Plan roles, Certificate compiled merged.core m (focus .high) 2 [] p ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness p m ⟨1,z⟩) := by
  have shared := exact_trace m valid
  constructor
  · have found := subtrace shared left_address.1 left_address.2
    obtain ⟨_,e,_,⟨hit,p,cert⟩,_⟩ := here found
    have each : read 1 = some ⟨2,[]⟩ := by
      change some (row .low) = _
      rw [GeneralSharedNamedCompiler310.row_exact]; rfl
    cases Option.some.inj (hit.symm.trans each)
    refine ⟨p,cert,cert.outputs _ ?_⟩
    exact List.mem_singleton_self _
  · have found := subtrace shared right_address.1 right_address.2
    obtain ⟨_,e,_,⟨hit,p,cert⟩,_⟩ := here found
    have each : read 2 = some ⟨2,[]⟩ := by
      change some (row .high) = _
      rw [GeneralSharedNamedCompiler310.row_exact]; rfl
    cases Option.some.inj (hit.symm.trans each)
    refine ⟨p,cert,cert.outputs _ ?_⟩
    exact List.mem_singleton_self _

end Yulang.GeneralSharedNamedTrace310
