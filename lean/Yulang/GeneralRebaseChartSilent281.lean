import Yulang.GeneralRebaseChartFixtures281
import Yulang.GeneralRebaseInstallPublicObstruction279
import Yulang.GeneralRebaseVersionAbsorb278
import Yulang.GeneralRebaseLooseAbsorb278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseChartSilent281
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseChartStep281 (Chart Public Recorded Strict Step)
open GeneralRebaseSemanticChart281 (Entails Gain Loss)
open GeneralRebaseProjectedEdgeCount279 (Seen Fresh)
open GeneralRebaseMixedCounts277 (Actual)

theorem quiet_chart {chart : Chart F V}
    (same : ∀ value, Public chart after value ↔ Public chart before value) :
    ¬ Gain chart.facts chart.meaning (Public chart) before after := by
  rintro ⟨f,_,absent,new⟩
  exact absent (fun value old => new value ((same value).mpr old))

theorem quiet_graph {before after : State roles}
    (same : after.core.erased.current.edges = before.core.erased.current.edges) :
    ¬ Fresh before after := by
  rintro ⟨edge,missing,new⟩
  exact missing (by simpa only [Seen,same] using new)

theorem no_strict {chart : Chart F V}
    (edges : after.core.erased.current.edges = before.core.erased.current.edges)
    (same : ∀ value, Public chart after value ↔ Public chart before value) :
    ¬ Strict chart before after :=
  fun move => move.elim (quiet_graph edges) (quiet_chart same)

theorem blocked {chart : Chart F V}
    (grows : after.plans.length ≠ before.plans.length)
    (edges : after.core.erased.current.edges = before.core.erased.current.edges)
    (same : ∀ value, Public chart after value ↔ Public chart before value) :
    ¬ Step chart r root before after :=
  fun step => step.2.elim grows (no_strict edges same)

def oldChart (facts : List F) (observes : F → Assignment → Prop) : Chart F Assignment :=
  ⟨facts,GeneralVersionBoundaryCompletion259.Agree,observes⟩

def looseChart (facts : List F) (observes : F → Assignment → Prop) : Chart F Assignment :=
  ⟨facts,GeneralDictionaryInitialProjection257.Agree,observes⟩

namespace Version
open GeneralDictionaryVersionLoopSource237 (sourceRegistry initial registry root)
open GeneralDictionaryVersionLoopIteration239 (state)
open GeneralRebaseVersionMicro278 (installed)
open GeneralRebaseInstallPublicObstruction279.Version (edges_equal public_iff)

theorem blocked_every (facts : List F) (observes : F → Assignment → Prop) (n : Nat) :
    ¬ Step (oldChart facts observes) sourceRegistry root (state n) (installed n) :=
  blocked (by change (_ :: (state n).plans).length ≠ (state n).plans.length; simp)
    (edges_equal n) (public_iff n)

theorem preserved_raw (n : Nat) : Actual sourceRegistry root (state n) (installed n) :=
  GeneralRebaseVersionMicro278.install_step n

theorem no_install {facts : List F} {observes : F → Assignment → Prop} {n : Nat} {target}
    (move : Step (oldChart facts observes) sourceRegistry root (state n) target) :
    target.plans = (state n).plans := by
  have reached : GeneralNominalVersionedMixedProgressSplit236.Reachable sourceRegistry root (state n) :=
    (GeneralDictionaryVersionLoopIteration239.stages n).reachable
  rcases GeneralNominalVersionedMixedProgressSplit236.split reached move.1 with admin|⟨e,enabled,novel,eq⟩
  · exact GeneralNominalVersionedMixedProgressSplit236.administrative_plans admin
  · have shell := GeneralRebaseVersionAbsorb278.terminal ⟨n,.enter⟩
    have framed := e.frame.raw_recorded
    have raw : (state n).core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := shell.raw
    rw [enabled.snapshot_eq,raw] at framed
    have rootEq : e.plan.packet.site.occurrence = root :=
      congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp framed)
    have existsInstall := (GeneralRebaseVersionAbsorb278.enter_install n target).mp
      ⟨e,rootEq.symm ▸ .root,enabled,novel,eq⟩
    exact False.elim (blocked_every facts observes n (existsInstall ▸ move))

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (sourceRegistry root)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralRebaseLooseMicro278 (installed)
open GeneralRebaseInstallPublicObstruction279.Loose (edges_equal public_iff)

theorem blocked_every (facts : List F) (observes : F → Assignment → Prop) (n : Nat) :
    ¬ Step (looseChart facts observes) sourceRegistry root (state n) (installed n) :=
  blocked (by change (_ :: (state n).plans).length ≠ (state n).plans.length; simp)
    (edges_equal n) (public_iff n)

theorem preserved_raw (n : Nat) : Actual sourceRegistry root (state n) (installed n) :=
  GeneralNominalPointErasure240.step_old (GeneralRebaseLooseMicro278.install_step n)

end Loose
end Yulang.GeneralRebaseChartSilent281
