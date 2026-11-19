import Yulang.GeneralRebaseCompiledFixtures282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseOptionalOverwrite282
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryOptionalInitial229 (declaration sourceRegistry)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed plan)
open GeneralRebaseTerminalRowFrame274 (oldPlan)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebasePrivateKey282 (port)
open GeneralRebaseTermAggregate281 (writes keys active address expression)
open GeneralRebaseWholeStore282 (store expression_exact)
open GeneralRebaseLiveOwner282 (newest newest_iff lookup_first)
open GeneralRebaseLiveStore282 (live)
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralRebaseTermCopy281 (Respects)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompoundPublic273 (Fixed)
open CommonNominalFullCarrier (Equivalent model subtype_refl)
open GeneralRebaseLoopBase282 (equiv_trans union_same)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralRebaseCompiledRegressions282 (phase_reachable)
open GeneralRebaseWholeJournal282 (source_visibility preserves_reads)
open Core.PresenceGeneration (TyTerm)

def lowerPort := port 4 root.identity declaration.id ⟨0,false,0⟩

theorem before_reached : Reachable sourceRegistry root before :=
  ⟨before,⟨GeneralDictionaryOptionalInitial229.start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,.refl⟩

theorem point_reached : Reachable sourceRegistry root point :=
  phase_reachable before_reached
    (.tail (.tail .refl GeneralRebasePhaseFixture281.first_kept) GeneralRebasePhaseFixture281.observe_kept)

theorem old_latest : oldPlan ∈ newest point.plans := by
  apply (newest_iff _ _).mpr
  change GeneralRebaseLiveOwner282.lookup [oldPlan] (GeneralRebasePhaseKeys281.owner oldPlan) = some oldPlan
  exact lookup_first _ _

theorem new_latest : plan ∈ newest installed.plans := by
  apply (newest_iff _ _).mpr
  change GeneralRebaseLiveOwner282.lookup (plan :: point.plans) (GeneralRebasePhaseKeys281.owner plan) = some plan
  exact lookup_first _ _

theorem old_write : (lowerPort,.union (.var 4) (.var 4)) ∈ writes oldPlan.packet true := by
  unfold writes keys active expression address
  change (_,_) ∈ (([0,0] : List Nat).flatMap _).map _
  simp only [GeneralDictionaryOptionalInstall229.bindings_exact]
  exact List.mem_cons_self

theorem new_write : (lowerPort,.union (.var 2) (.var 2)) ∈ writes plan.packet true := by
  unfold writes keys active expression address
  change (_,_) ∈ (([0,0] : List Nat).flatMap _).map _
  simp only [GeneralDictionaryVersionedPoint233.bindings_exact]
  exact List.mem_cons_self

theorem read_lower {s : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles}
    (reach : Reachable sourceRegistry root s) {p : GeneralNominalCenters.Plan GeneralDictionaryJournalRefinement228Source.roles}
    (selected : p ∈ newest s.plans) {id : Nat}
    (known : id ≤ (raw s).seed) (write : (lowerPort,.union (.var id) (.var id)) ∈ writes p.packet true)
    (m : Assignment) (all : Respects (live s) m) :
    Equivalent (m lowerPort).1 (m id).1 := by
  let t : TyTerm Nat := .union (.var id) (.var id)
  have compiled : (lowerPort,t.subst (mapping (history s))) ∈ store s p.packet :=
    List.mem_map.mpr ⟨(lowerPort,t),write,rfl⟩
  have h := all _ (List.mem_flatMap.mpr ⟨p,selected,compiled⟩)
  change Equivalent (m lowerPort).1 ((t.subst (mapping (history s))).eval model m) at h
  rw [expression_exact] at h
  have safe := (source_visibility reach [id] (fun _ member => List.mem_singleton.mp member ▸ known)).1
  have agree := congrArg Prod.fst (preserves_reads safe m id (List.mem_singleton_self _))
  have normalized : Equivalent (t.eval model (decode s m)) (decode s m id).1 := union_same _
  rw [agree] at normalized
  exact equiv_trans h normalized

theorem old_lower (m : Assignment) (held : Respects (live point) m) :
    Equivalent (m lowerPort).1 (m 4).1 :=
  read_lower point_reached old_latest (by decide +kernel) old_write m held

theorem new_lower (m : Assignment) (held : Respects (live installed) m) :
    Equivalent (m lowerPort).1 (m 2).1 :=
  read_lower GeneralRebaseTerminalMixedRefresh274.mixed_reachable new_latest (by decide +kernel) new_write m held

theorem stale_append_fails (m : Assignment) (publicFixed : Fixed m)
    (beforeTable : Respects (live point) m) (afterTable : Respects (live installed) m) : False := by
  have old := old_lower m beforeTable
  have current := new_lower m afterTable
  have body := publicFixed 4 (by decide)
  have width := publicFixed 2 (by decide)
  exact GeneralDictionaryOptionalOutput229.not_width
    (equiv_trans ⟨body.2,body.1⟩ (equiv_trans ⟨old.2,old.1⟩ (equiv_trans current width)))

end Yulang.GeneralRebaseOptionalOverwrite282
