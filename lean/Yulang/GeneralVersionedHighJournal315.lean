import Yulang.GeneralVersionedHighClass315
import Yulang.GeneralVersionedObservedEssential313

set_option backward.isDefEq.respectTransparency false
/-! The old mixed source journal has no support above purpose 9. Keep this
result distinct from allocation under the proposed endpoint representation. -/
namespace Yulang.GeneralVersionedHighJournal315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedHighOrigins315 (Absent raw_absent)
open GeneralVersionedHighPacket315 (registered registered_raw)
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedEssentialSupport313 (Inert Essential)

theorem legacy {s : State roles} {k : Origin} (actual : Reachable registry root s) (tag : 9 < k.2.2.1) :
    ∀ n ∈ journalSources s.legacy, Absent s k n := by
  obtain ⟨emptyPlan,emptyEffect⟩ := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty actual
  intro n member
  simp only [journalSources,List.mem_append] at member
  rcases member with (((((raw|base)|rawSite)|site)|past)|effect)
  · exact fun eq => raw_absent actual tag (eq ▸ GeneralDictionaryDefaultRawSupport213.subset _ raw)
  · exact fun eq => raw_absent actual tag (eq ▸ GeneralVersionedOwnerEnvelope314.initial_source_subset actual
      (GeneralDictionaryDefaultRawSupport213.subset _ base))
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp rawSite
    exact registered_raw actual tag site present n inside
  · obtain ⟨site,present,inside⟩ := List.mem_flatMap.mp site
    exact registered actual tag site present n inside
  · rw [show s.legacy.core.plans = [] from emptyPlan] at past
    cases past
  · rw [emptyEffect] at effect
    cases effect

theorem all {s : State roles} {k : Origin} (actual : Reachable registry root s) (tag : 9 < k.2.2.1) :
    ∀ n ∈ sources s, Absent s k n := by
  intro n member
  rcases List.mem_append.mp member with first|last
  · rcases List.mem_append.mp first with old|stored
    · exact legacy actual tag n old
    · obtain ⟨p,history,within⟩ := List.mem_flatMap.mp stored
      exact GeneralVersionedHighPacket315.stored_sources actual tag history n within
  · obtain ⟨e,history,within⟩ := List.mem_flatMap.mp last
    exact GeneralVersionedHighClass315.effect_frame actual tag history n within


open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedEndpointAddress315 (Side atCell key)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty)

theorem unused {s : State roles} {k : Origin} (actual : Reachable registry root s) (tag : 9 < k.2.2.1) :
    source (seed s) k ∉ sources s :=
  fun inside => all actual tag _ inside rfl

def patch (m : Assignment) (id : Nat) (ty : Ty) : Assignment :=
  fun i => if i = id then (ty,(m i).2) else m i

theorem patch_preserves {s : State roles} {k : Origin}
    (actual : Reachable registry root s) (tag : 9 < k.2.2.1)
    (m : Assignment) (ty : Ty) :
    Models s (patch m (source (seed s) k) ty) ↔ Models s m := by
  apply (GeneralNominalVersionedModelSupport237.current s m _ (fun n present => ?_)).symm
  have different := all actual tag n present
  simp [patch,different]

theorem proposed_patch_preserves {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s)
    (side : Side) (clause pos : Nat) (expr : Expr) (m : Assignment) (ty : Ty) :
    Models s (patch m (atCell p side clause pos expr) ty) ↔ Models s m := by
  unfold atCell
  have alignedSeed : p.packet.context.state.seed = seed s := congrArg (fun c => c.state.seed) aligned
  rw [alignedSeed]
  apply patch_preserves actual
  change 9 < side.purpose
  cases side <;> decide

end Yulang.GeneralVersionedHighJournal315
