import Yulang.GeneralDeclarativeCurrentProposal345
import Yulang.GeneralDeclarativeCurrentPeerOutput345

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeCurrentUnstored345
open GeneralLatePeerSource311 (registry compiled root checked)
open GeneralLatePeerRoot311 (z direct branch)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerMerge311 (final reached child_new child_root child_branch inherited)
open GeneralLatePeerFinalPeerPlan311 (plan)
open GeneralLatePeerJoint311 (effect enabled)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeCurrentJoint345 (Block)
open GeneralDeclarativeCurrentPeer345 (after_row row)
open GeneralDeclarativeCurrentOrder345 (rows)
open CommonRoleOutermostResolver (All₂)

theorem committed_current : Committed final plan := by
  refine ⟨?_,?_⟩
  · intro m fit
    exact ⟨GeneralLatePeerFinalPeerPlan311.holds m fit,GeneralLatePeerCurrent311.classes m fit⟩
  · intro x member
    rw [GeneralLatePeerFinalPeerPlan311.no_children] at member
    cases member

theorem no_effect_at_child :
    ∀ e ∈ final.effects, e.plan.packet.site.occurrence.identity ≠ child.occurrence.identity := by
  intro e present
  change e ∈ [GeneralLatePeerRouteInstall311.effect,GeneralLatePeerDirectInstall311.effect,
    GeneralLatePeerFirst311.effect] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact Ne.symm child_branch
  · exact Ne.symm child_new
  · exact Ne.symm child_root

theorem unstored : effect ∉ final.effects := by
  intro has
  exact (no_effect_at_child effect has) rfl

private theorem find_pair (good : All₂ P xs ys) (member : x ∈ xs) : ∃ y ∈ ys,P x y := by
  induction good with
  | nil => cases member
  | cons pair remains ih =>
    rcases List.mem_cons.mp member with rfl|later
    · exact ⟨_,List.mem_cons_self,pair⟩
    · obtain ⟨_,there,witness⟩ := ih later
      exact ⟨_,List.mem_cons_of_mem _ there,witness⟩

/-- The actually reached late peer has a committed current packet and
a genuine inherited nonempty output even though no effect was stored
at this occurrence. It must not be explained as an installed child. -/
theorem actual (m : Assignment) (fit : Models final m) :
    effect ∉ final.effects ∧
    ∃ equations, Block registry root final effect equations ∧
      ∃ e ∈ equations, e.left = z ∧ Holds m e := by
  obtain ⟨equations,placed,sound,_⟩ := GeneralDeclarativeCurrentProposal345.actual_current
    ⟨rfl,checked⟩ reached enabled.registry_eq enabled.snapshot_eq committed_current m fit
  obtain ⟨e,member,made⟩ := find_pair placed after_row
  exact ⟨unstored,equations,placed,e,member,made.2.1,sound _ member⟩

end Yulang.GeneralDeclarativeCurrentUnstored345
