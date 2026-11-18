import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralNominalCompleteNames183
namespace Yulang.GeneralNominalInputOccurrences256
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveInspection GeneralNominalAllocation

/-- The source frame already contains finished inspection, without requiring
an all-model packet certificate. -/
theorem frame_finished
 (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan) :
 Finished (GeneralNominalRecursiveCandidates.report plan.packet.context
   plan.packet.declaration plan.packet.bounds) := by
 have prepared : GeneralNominalVersionedCandidates231.Prepared registry plan.packet.context root plan.packet.declaration :=
   frame.context_eq.symm ▸ frame.prepared
 obtain ⟨_,_,bounds,located,_,done,_⟩ := prepared
 have same : bounds = plan.packet.bounds := Option.some.inj (located.symm.trans frame.located)
 subst bounds
 exact done

theorem report_nonempty (context : GeneralNominalCandidates.Context)
 (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
 (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds))
 (name : Nat) (named : name ∈ declaration.inputNames) :
 occurrences (bindings context.state (GeneralNominalRecursiveCandidates.report context declaration bounds)) name ≠ [] := by
 have done : Finished (inspectMany context.state
   (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds (fun _ => none) 0) := finished
 obtain ⟨capture,member,same⟩ := GeneralNominalCompleteNames183.declaration_input_capture
   context.state context.interpretation declaration bounds (fun _ => none) 0 done name named
 have found : (context.state.base.source capture.bounds.1,context.state.base.source capture.bounds.2) ∈
   occurrences (bindings context.state (GeneralNominalRecursiveCandidates.report context declaration bounds)) name := by
   apply List.mem_map.mpr
   refine ⟨(capture.name,context.state.base.source capture.bounds.1,context.state.base.source capture.bounds.2),?_,rfl⟩
   apply List.mem_filter.mpr
   constructor
   · exact List.mem_map.mpr ⟨capture,member,rfl⟩
   · simp only [same,beq_self_eq_true]
 intro empty
 rw [empty] at found
 cases found

theorem frame_nonempty
 (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
 occurrences (bindings plan.packet.context.state
   (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds)) name ≠ [] :=
 report_nonempty _ _ _ (frame_finished frame) name named
end Yulang.GeneralNominalInputOccurrences256
