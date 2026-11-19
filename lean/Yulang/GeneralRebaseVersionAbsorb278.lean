import Yulang.GeneralRebaseVersionRefreshLeaf278
import Yulang.GeneralRebaseTerminalAbsorb278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseVersionAbsorb278
open GeneralDictionaryVersionLoopSource237 (roles registry root declaration model source_model)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralDictionaryVersionLoopFrame239 (children_empty emitted_empty raw_children_empty)
open GeneralDictionaryVersionLoopInstall239 (chosen installable)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseVersionMicro278 (raw installed refreshed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseTerminalAbsorb278 (Terminal InstallTransition)
open GeneralNominalCenters (rootSite)

theorem packed_edges (n : Nat) : GeneralNominalVersionedChildren232.edges (plan n) = [] := by
  unfold GeneralNominalVersionedChildren232.edges
  rw [children_empty]
  rfl

theorem stage_edges (n : Nat) : (state n).core.erased.current.edges = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (state n).core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges (plan n) = []
    rw [ih,packed_edges]
    rfl

theorem terminal (t : Tick) : Terminal registry (raw t) root := by
  rcases t with ⟨n,p⟩
  have oldRaw := (stages n).shape.rawSites
  have oldCenters := (stages n).shape.centers
  have oldEdges := stage_edges n
  cases p
  · exact ⟨⟨declaration,rfl⟩,oldRaw,⟨_,oldCenters⟩,oldEdges⟩
  all_goals
    refine ⟨⟨declaration,rfl⟩,?_,⟨rootSite 3 root,?_⟩,?_⟩
    · change (state n).core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (plan n) =
        [GeneralNominalDemandMerging.pointSite root]
      rw [oldRaw,raw_children_empty]
      rfl
    · change (state n).core.sites ++ GeneralNominalVersionedChildren232.emitted (plan n) = [rootSite 3 root]
      rw [oldCenters,emitted_empty]
      rfl
    · change (state n).core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges (plan n) = []
      rw [oldEdges,packed_edges]
      rfl

theorem enter_install (n : Nat) (t : State roles) :
  InstallTransition registry root (state n) t ↔ t = installed n := by
  have yes := installable (stages n).shape (stages n).valid (stages n).recorded
  exact ⟨GeneralRebaseTerminalAbsorb278.deterministic_install (terminal ⟨n,.enter⟩)
    (chosen (stages n).shape) yes rfl t,
    by rintro rfl; exact ⟨_,.root,yes,GeneralDictionaryVersionLoopStage239.novel (stages n),rfl⟩⟩

theorem installed_absorbs (n : Nat) (t : State roles) :
    ¬ InstallTransition registry root (installed n) t :=
  GeneralRebaseTerminalAbsorb278.no_install (terminal ⟨n,.installed⟩)
    (GeneralRebaseVersionRefreshLeaf278.ready_rule n _
      (GeneralRebaseVersionMicro278.complete_all ⟨n,.installed⟩ model source_model)) t

theorem refreshed_absorbs (n : Nat) (t : State roles) :
    ¬ InstallTransition registry root (refreshed n) t :=
  GeneralRebaseTerminalAbsorb278.no_install (terminal ⟨n,.refreshed⟩)
    (GeneralRebaseVersionRefreshLeaf278.refreshed_rule n _
      (GeneralRebaseVersionMicro278.complete_all ⟨n,.refreshed⟩ model source_model)) t

end Yulang.GeneralRebaseVersionAbsorb278
