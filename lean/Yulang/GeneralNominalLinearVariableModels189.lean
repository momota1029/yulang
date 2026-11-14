import Yulang.GeneralNominalSingleVariableModels189

/-! Same-assignment private head models for finite linear variable heads.
The list records each distinct capture name and its point argument slot. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalLinearVariableModels189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

private theorem filter_key {α : Type} (entries : List (Nat × α))
    (unique : (entries.map Prod.fst).Nodup) (entry : Nat × α) (member : entry ∈ entries) :
    entries.filter (fun other => other.1 == entry.1) = [entry] := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    have uniq := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.filter_cons,beq_self_eq_true,ite_true,List.cons.injEq,true_and]
      simp only [List.filter_eq_nil_iff]
      intro other present
      intro same
      exact uniq.1 (List.mem_map.mpr ⟨other,present,by simpa using same⟩)
    · have different : head.1 ≠ entry.1 := by
        intro same
        exact uniq.1 (List.mem_map.mpr ⟨entry,member,same.symm⟩)
      simp [different,ih uniq.2 member]

private theorem linear_report (state : GeneralNominalState.State)
    (entries : List (Nat × Fin state.base.slots)) (index : Nat) :
    inspectMany state (entries.map fun entry => .variables [entry.1])
      (entries.map fun entry => (entry.2,entry.2)) (fun _ => none) index =
    { captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
      checked := entries.map (fun entry => (entry.2,entry.2)) } := by
  induction entries generalizing index with
  | nil => simp [inspectMany]
  | cons head tail ih =>
      simp [inspectMany,inspect,Report.append,ih]

theorem head_models (candidate : Plan roles)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (unique : (entries.map Prod.fst).Nodup)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration =
        entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (model : Assignment) (valid : GeneralNominalState.Models candidate.packet.context.state model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  have reportEq : GeneralNominalPacketSupport.report candidate.packet =
      ({ captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
         checked := (entries.map fun entry => (entry.2,entry.2)) ++
           (entries.map fun entry => (entry.2,entry.2)) } : Report candidate.packet.context.state) := by
    simp [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,
      query,bounds,linear_report]
  have bindingsEq : candidate.packet.bindings = entries.map (fun entry =>
      (entry.1,candidate.packet.context.state.base.source entry.2,
        candidate.packet.context.state.base.source entry.2)) := by
    change bindings _ (GeneralNominalPacketSupport.report candidate.packet) = _
    rw [reportEq]
    simp [bindings,List.map_map]
  have occurs (entry : Nat × Fin candidate.packet.context.state.base.slots) (member : entry ∈ entries) :
      GeneralNominalAllocation.occurrences candidate.packet.bindings entry.1 =
      [(candidate.packet.context.state.base.source entry.2,
        candidate.packet.context.state.base.source entry.2)] := by
    rw [bindingsEq]
    simp only [GeneralNominalAllocation.occurrences,List.filter_map,List.map_map,Function.comp_def]
    change List.map (fun entry => (candidate.packet.context.state.base.source entry.2,
      candidate.packet.context.state.base.source entry.2))
        (entries.filter (fun other => other.1 == entry.1)) = _
    rw [filter_key entries unique entry member]
    rfl
  rw [GeneralNominalHeadBranchFrame187.head_models_exact,GeneralNominalPacketSupport.private_exact]
  refine ⟨⟨valid,?_,?_,?_⟩,?_⟩
  · rw [bindingsEq]
    intro first one last two same
    obtain ⟨a,am,rfl⟩ := List.mem_map.mp one
    obtain ⟨b,bm,rfl⟩ := List.mem_map.mp two
    have found : b ∈ entries.filter (fun other => other.1 == a.1) :=
      List.mem_filter.mpr ⟨bm,by simpa using same.symm⟩
    rw [filter_key entries unique a am] at found
    have equal := List.mem_singleton.mp found
    subst b
    exact subtype_refl _
  · intro atom member
    unfold GeneralNominalAllocation.merges at member
    obtain ⟨name,present,member⟩ := List.mem_flatMap.mp member
    rw [names] at present
    obtain ⟨entry,entryMem,rfl⟩ := List.mem_map.mp present
    rw [occurs entry entryMem] at member
    cases member
  · rw [reportEq]
    intro atom member
    unfold selfChecks at member
    obtain ⟨pair,pairMem,rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp pairMem with member | member <;>
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member <;> exact subtype_refl _
  · rw [reportEq]
    refine ⟨by simp,by simp,?_,?_⟩
    · intro first one last two same ref origin actual seen
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp one
      cases origin
    · intro first one last two same a b origin other x y seenX seenY
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp one
      cases origin

end Yulang.GeneralNominalLinearVariableModels189
