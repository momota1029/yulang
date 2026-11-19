import Yulang.GeneralRebaseVersionRetained278
import Yulang.GeneralRebaseNonleafTransport276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseVersionRefreshLeaf278
open GeneralDictionaryVersionLoopSource237 (roles registry sourceRegistry root declaration snapshot)
open GeneralDictionaryVersionLoopIteration239 (stages)
open GeneralDictionaryVersionLoopBook239 (plan allocations reservations atoms)
open GeneralDictionaryVersionLoopFamilyBase238 (original pair)
open GeneralDictionaryVersionLoopInstall239 (chosen installed_recorded)
open GeneralDictionaryVersionLoopFrame239 (children_empty)
open GeneralRebaseVersionMicro278 (installed refreshed)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRetarget275 (Observed)
open GeneralRebaseNonleafTransport276 (ReadyRule rule_refresh leaf_or_node)

noncomputable abbrev replay (n : Nat) := replayPlan (plan n)

theorem replay_observed (n : Nat) : Observed (replay n) := by
  unfold Observed
  have query : GeneralNominalInspection.queries (replay n).packet.context.state
      (replay n).packet.context.interpretation (replay n).packet.declaration =
      [.nominal 5 [.variables [0],.variables [0]]] :=
    GeneralDictionaryVersionLoopFamilyPacket238.query n (allocations n) (reservations n) (atoms n)
  rw [query]
  change GeneralNominalRefinementTrace197.ObservedMany (replay n).packet.context.state _
    [(original n 3,original n 3)]
  exact .cons (.point (descriptor := pair n) rfl rfl rfl
    (.cons .variables (.cons .variables .nil))) .nil

noncomputable def refresh_certificate (n : Nat) :=
  GeneralDictionaryVersionLoopFamilyRefresh238.certificate allocations reservations atoms (installed n) n
    (stages n).shape.source rfl (installed_recorded (stages n).shape (stages n).recorded)

theorem ready_rule (n : Nat) (m : Assignment) (valid : Models (installed n) m) :
    ReadyRule registry (installed n) root 0 [] := by
  refine ⟨replay n,?_,replay_observed n,?_,?_,((replay_children (plan n)).trans (children_empty n)).symm⟩
  · exact GeneralNominalVersionedInstalledEvidence233.frame (effect := chosen (stages n).shape) rfl valid
  · exact GeneralNominalVersionedCommitted232.replay_committed (stages n).state (chosen (stages n).shape)
  · exact GeneralNominalVersionedInstalledEvidence233.ready (effect := chosen (stages n).shape) rfl (children_empty n)

theorem refreshed_rule (n : Nat) (m : Assignment) (valid : Models (refreshed n) m) :
    ReadyRule registry (refreshed n) root 0 [] :=
  rule_refresh (refresh_certificate n) m valid
    (ready_rule n m ((GeneralRebaseVersionPrivate278.refreshed_exact n m).mp valid))

theorem refreshed_leaf (n : Nat) (m : Assignment) (valid : Models (refreshed n) m) :
    Evidence registry (refreshed n).core m root (.node 0 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf (leaf_or_node m valid (refreshed_rule n m valid))

theorem refreshed_shape (n : Nat) (m : Assignment) (valid : Models (refreshed n) m)
    (data : GeneralDictionaryReadback.Payload) :
    Evidence registry (refreshed n).core m root data ↔ data = .node 0 [] := by
  constructor
  · exact GeneralRebaseTerminalEvidence278.leaf_shape (d := declaration) rfl rfl
  · rintro rfl
    exact refreshed_leaf n m valid

theorem retained_all_leaves (m : Assignment) (valid : GeneralRebaseVersionRetained278.Settled m)
    (t : GeneralRebaseRoundMicro278.Tick) :
    Evidence registry (GeneralRebaseVersionMicro278.raw t).core
      (GeneralRebaseVersionRetained278.retain m) root (.node 0 []) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact GeneralRebaseVersionEvidence278.enter_leaf n _ (GeneralRebaseVersionRetained278.packet_retained m valid n)
  · exact GeneralRebaseVersionEvidence278.installed_leaf n _
      (GeneralRebaseVersionRetained278.micro_retained m valid ⟨n,.installed⟩)
  · exact refreshed_leaf n _ (GeneralRebaseVersionRetained278.micro_retained m valid ⟨n,.refreshed⟩)

end Yulang.GeneralRebaseVersionRefreshLeaf278
