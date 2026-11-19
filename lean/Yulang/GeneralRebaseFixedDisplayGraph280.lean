import Yulang.GeneralRebasePortGate280
import Yulang.GeneralRebaseFixedGraphExec280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseFixedDisplayGraph280
open GeneralNominalExamples (displayRoot displayChild registry state)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseCompiledDisplay277 (compiled parent effect after frame_parent)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseDisplayStep276 (initial_source)
open GeneralRebaseCompiledInstall277 (adapter_step)
open GeneralRebaseFixedDisplay280 (canonical actual c valid raw_occurrence)
open GeneralRebaseFixedGraph280 (Recode RecodeEdge)
open GeneralRebaseFixedGraphExec280 (edgeCodes edgeCode write_exact recode)
open GeneralRebasePortCatalog280 (Parents catalog resolve code)

theorem baked : (boundary roles).Checked registry := ⟨rfl,GeneralNominalExamples.registry_checked⟩

theorem actual_edge_list : after.core.erased.current.edges = [(displayRoot,displayChild)] := by
  change [] ++ GeneralNominalVersionedChildren232.edges parent = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [GeneralRebaseCompiledDisplay277.children]
  rfl

theorem parent_catalog : Parents after = [100] := by
  unfold Parents
  rw [actual_edge_list]
  rfl

theorem matched : Recode compiled (state true).seed displayRoot displayChild canonical.occurrence := by
  have invariant := GeneralNominalVersionedMixedCompletionRequests235.trace
    (B4Target.Steps.refl : B4Target.Steps
      (GeneralNominalVersionedMixedKernel234.Step compiled displayRoot) before before)
  have clauseMem : c ∈ parent.packet.declaration.requirements := List.mem_singleton_self _
  have same := GeneralRebaseFixedGraph280.child_recode invariant frame_parent clauseMem valid
  exact raw_occurrence ▸ same

theorem recoded : RecodeEdge compiled (state true).seed displayRoot (displayRoot,displayChild)
    (displayRoot,canonical.occurrence) :=
  ⟨GeneralRebaseFixedGraph280.root_recode ..,matched⟩

theorem fixed_edge_list :
    edgeCodes compiled (state true).seed displayRoot after =
      [edgeCode (displayRoot,canonical.occurrence)] := by
  have actual : (displayRoot,displayChild) ∈ after.core.erased.current.edges :=
    actual_edge_list.symm ▸ List.mem_singleton_self _
  have step := write_exact initial_source baked (.tail .refl adapter_step) actual recoded
  change recode (catalog compiled (state true).seed displayRoot (Parents after)) (displayRoot,displayChild) =
    some (edgeCode (displayRoot,canonical.occurrence)) at step
  unfold edgeCodes
  rw [actual_edge_list]
  simp only [List.filterMap_cons,step,List.filterMap_nil]
  rfl

theorem explicit_read :
    resolve (catalog compiled (state true).seed displayRoot [100]) displayChild.identity =
      some (code roles (state true).seed 100 parent.packet.declaration c) := by
  have h := GeneralRebaseFixedGraphExec280.exact_read initial_source baked (.tail .refl adapter_step)
    ((GeneralRebaseFullEdgeBasis279.endpoints initial_source (.tail .refl adapter_step) (displayRoot,displayChild)
      (actual_edge_list.symm ▸ List.mem_singleton_self _)).2) matched
  change resolve (catalog compiled (state true).seed displayRoot (Parents after)) displayChild.identity = _ at h
  rw [parent_catalog] at h
  exact h

end Yulang.GeneralRebaseFixedDisplayGraph280
