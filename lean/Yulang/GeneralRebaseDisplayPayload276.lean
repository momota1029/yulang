import Yulang.GeneralRebaseDisplayExecutor276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9600000
namespace Yulang.GeneralRebaseDisplayPayload276
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (after)
open GeneralRebaseDisplayExecutor276 (Goal invocation)
open GeneralRebaseDisplayStable276 (framed_parent framed_child)
open GeneralRebaseDisplaySelection276 (parent_children)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence payload_iff_erased)

def accepts : Goal → Payload → Bool
 | .parent,.node parentKey [.node childKey []] => parentKey == 1 && childKey == 3
 | .child,.node childKey [] => childKey == 3
 | _,_ => false

theorem child_shape (m : Assignment) (data : Payload)
 (valid : Evidence registry after.core m displayChild data) : data = .node 3 [] := by
 have reported := (payload_iff_erased _ _ _).mpr valid
 cases reported with
 | node rule ordered =>
   obtain ⟨p,recorded⟩ := rule
   have pEq := framed_child recorded.frame
   subst p
   have keyEq := recorded.frame.key_eq
   rw [recorded.children_eq,GeneralRebaseDisplayChild276.no_children] at ordered
   cases ordered
   rw [←keyEq]

theorem parent_shape (m : Assignment) (data : Payload)
 (valid : Evidence registry after.core m displayRoot data) : data = .node 1 [.node 3 []] := by
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

theorem child_accepts (data : Payload) : accepts .child data = true ↔ data = .node 3 [] := by
 cases data with
 | node k ds =>
   cases ds <;> simp [accepts]

theorem parent_accepts (data : Payload) : accepts .parent data = true ↔ data = .node 1 [.node 3 []] := by
 cases data with
 | node root ds =>
   cases ds with
   | nil => simp [accepts]
   | cons first rest =>
     cases rest with
     | cons => simp [accepts]
     | nil =>
       cases first with
       | node key children =>
         cases children <;> simp [accepts]

theorem exact (goal : Goal) (m : Assignment) (valid : Models after m) (data : Payload) :
 accepts goal data = true ↔ Evidence registry after.core m (invocation goal) data := by
 cases goal
 · rw [parent_accepts]
   exact ⟨fun same => same.symm ▸ GeneralRebaseDisplayEvidence276.real_nonleaf m valid,parent_shape m data⟩
 · rw [child_accepts]
   exact ⟨fun same => same.symm ▸ GeneralRebaseDisplayEvidence276.child_evidence m valid,child_shape m data⟩

theorem no_parent_leaf : accepts .parent (.node 1 []) = false := rfl
theorem no_dangling_child : accepts .parent (.node 1 [.node 1 []]) = false := rfl
theorem no_redundant_child : accepts .parent (.node 1 [.node 3 [],.node 3 []]) = false := rfl

end Yulang.GeneralRebaseDisplayPayload276
