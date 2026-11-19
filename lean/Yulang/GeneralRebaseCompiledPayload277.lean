import Yulang.GeneralRebaseCompiledStable277
import Yulang.GeneralRebaseDisplayPayload276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9600000
namespace Yulang.GeneralRebaseCompiledPayload277
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (after compiled)
open GeneralRebaseDisplayExecutor276 (Goal invocation)
open GeneralRebaseCompiledStable277 (framed_parent framed_child)
open GeneralRebaseCompiledSelection277 (parent_children)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence payload_iff_erased)

open GeneralRebaseDisplayPayload276 (accepts child_accepts parent_accepts)

theorem child_shape (m : Assignment) (data : Payload)
 (valid : Evidence compiled after.core m displayChild data) : data = .node 3 [] := by
 have reported := (payload_iff_erased _ _ _).mpr valid
 cases reported with
 | node rule ordered =>
   obtain ⟨p,recorded⟩ := rule
   have pEq := framed_child recorded.frame
   subst p
   have keyEq := recorded.frame.key_eq
   rw [recorded.children_eq,GeneralRebaseCompiledChild277.no_children] at ordered
   cases ordered
   rw [←keyEq]

theorem parent_shape (m : Assignment) (data : Payload)
 (valid : Evidence compiled after.core m displayRoot data) : data = .node 1 [.node 3 []] := by
 have reported := (payload_iff_erased _ _ _).mpr valid
 cases reported with
 | node rule ordered =>
   obtain ⟨p,recorded⟩ := rule
   have pEq := framed_parent recorded.frame
   subst p
   have keyEq := recorded.frame.key_eq
   rw [recorded.children_eq,parent_children] at ordered
   cases ordered with
   | cons current tail =>
     have eq := child_shape m _ ((payload_iff_erased _ _ _).mp current)
     cases tail
     rw [eq,←keyEq]
     rfl

theorem exact (goal : Goal) (m : Assignment) (valid : Models after m) (data : Payload) :
 accepts goal data = true ↔ Evidence compiled after.core m (invocation goal) data := by
 cases goal
 · rw [parent_accepts]
   exact ⟨fun same => same.symm ▸ GeneralRebaseCompiledEvidence277.real_nonleaf m valid,parent_shape m data⟩
 · rw [child_accepts]
   exact ⟨fun same => same.symm ▸ GeneralRebaseCompiledEvidence277.child_evidence m valid,child_shape m data⟩

theorem adapter_exact (goal : Goal) (m : Assignment) (valid : Models after m) (data : Payload) :
 accepts goal data = true ↔ (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Evidence
    registry after m (invocation goal) data := exact goal m valid data

end Yulang.GeneralRebaseCompiledPayload277
