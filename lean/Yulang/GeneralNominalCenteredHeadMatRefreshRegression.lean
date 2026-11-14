import Yulang.GeneralNominalCenteredHeadMatRefreshRegressionControl

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatRefreshRegression
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSourceUnsettledRefreshWitness
open GeneralNominalCenteredSourceUnsettledRefreshDecision (controlContext controlSource)
open GeneralNominalCenteredHeadMatRefreshRegressionSource
open GeneralNominalCenteredHeadMatRefreshRegressionTrace
open GeneralNominalCenteredHeadMatRefreshRegressionControl
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepBoundary (Local boundary)
open GeneralNominalCenteredHeadCandidates (inputs)

theorem r_arguments : GeneralNominalRecursiveCandidates.arguments controlContext (inputs emittedChild.occurrence) = some [(1,1)] :=
  GeneralNominalCenteredSourceUnsettledRefreshDecision.control_arguments

theorem r_blocked : (GeneralNominalRecursiveCandidates.report controlContext r [(1,1)]).blocked = [(2,2)] := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [GeneralNominalCenteredSourceUnsettledRefreshDecision.control_queries]
  simp only [GeneralNominalRecursiveInspection.inspectMany.eq_2,
    GeneralNominalRecursiveInspection.inspectMany.eq_1,GeneralNominalRecursiveInspection.inspect.eq_4]
  change ((GeneralNominalRecursiveInspection.inspectMany controlSource
    [.scalar .int,.variables [1]] [(2,2),(2,2)] (fun _ => none) 0).blocked ++ []) = [(2,2)]
  simp [GeneralNominalRecursiveInspection.inspectMany.eq_2,
    GeneralNominalRecursiveInspection.inspectMany.eq_1,GeneralNominalRecursiveInspection.inspect.eq_1,
    GeneralNominalRecursiveInspection.inspect.eq_3,GeneralNominalRecursiveInspection.Report.append,
    GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.block,
    controlSource,GeneralNominalCenteredSourceUnsettledRefreshDecision.controlView,refreshedView]

theorem r_not_prepared : ¬ GeneralNominalCenteredHeadCandidates.Prepared registry controlContext emittedChild.occurrence r := by
  rintro ⟨_,_,_,bounds,located,finished,_⟩
  have boundsEq := Option.some.inj (located.symm.trans r_arguments)
  subst bounds
  have blocked := finished.1
  rw [r_blocked] at blocked
  cases blocked

theorem r_not_failed : ¬ GeneralNominalCenteredHeadCandidates.Failed registry controlContext emittedChild.occurrence r := by
  rintro ⟨_,_,bounds,located,blocked,_⟩
  have boundsEq := Option.some.inj (located.symm.trans r_arguments)
  subst bounds
  rw [r_blocked] at blocked
  cases blocked

theorem r_known : ¬ GeneralNominalState.RootPending controlSource (inputs emittedChild.occurrence).demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  change GeneralNominalState.Known controlSource (emittedChild.occurrence.demand.arguments index).1
  rw [childP_arguments childSignature index]
  exact ⟨(1 : Fin 5),rfl,Or.inl (by intro impossible; cases impossible)⟩

theorem r_pending : Local registry kept emittedChild.occurrence .pending := by
  apply B4TargetV6.Local.inspectionPending
  · exact r_known
  · exact Or.inl ⟨r_known,r,List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,r_not_failed,r_not_prepared⟩
  · rintro (⟨_,_,_,slot,_,cycle⟩ | (⟨index,cycle⟩ | ⟨site,member,same,index,cycle⟩))
    · exact GeneralNominalCenteredSourceUnsettledRefreshDecision.control_no_raw slot
        (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
    · exact no_cycles kept_model _ cycle
    · exact no_cycles kept_model _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨plan,frame,entry,present,cycle⟩)
    · exact GeneralNominalCenteredSourceUnsettledRefreshDecision.control_no_raw visited.1
        (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
    · exact no_cycles kept_model _ cycle

theorem r_not_installable (effect : Effect roles)
    (focus : effect.plan.packet.site.occurrence = emittedChild.occurrence) :
    ¬ GeneralNominalCenteredHeadMatStepKernel.Installable registry kept effect := by
  intro enabled
  have selected := GeneralNominalCenteredHeadMatStepBoundary.local_iff.mpr
    (GeneralNominalCenteredHeadMatStepKernel.installable_selected enabled)
  rw [focus] at selected
  have impossible := GeneralNominalCenteredHeadMatStepBoundary.local_functional r_pending selected
  cases impossible

theorem no_r_packet (packet : GeneralNominalSaturationState.Packet roles)
    (present : packet ∈ kept.core.erased.current.packets) : packet.declaration = p := by
  cases List.mem_singleton.mp present
  rfl

theorem preserved_parent_head : controlSource.view.heads 1 = .structural 0 (fun _ => 2) := rfl

theorem r_generated : GeneralNominalSaturationState.Generated kept.core.erased.current root emittedChild.occurrence :=
  .child .root (installed_child (effect := effectP) (childrenP_exact ▸ List.mem_singleton_self _))

theorem decisive_regression :
    Checked registry ∧ GeneralNominalSourceFormation.InitialSource registry context root ∧
    GeneralNominalActualBudget.PointSource context root ∧ GeneralNominalCenteredHeadWFSource.Coverage registry interpretation ∧
    B4Target.Steps (GeneralNominalCenteredHeadMatStepKernel.Step registry root) start kept ∧
    Models kept witness ∧ Local registry kept emittedChild.occurrence .pending ∧
    (∀ effect : Effect roles, effect.plan.packet.site.occurrence = emittedChild.occurrence →
      ¬ GeneralNominalCenteredHeadMatStepKernel.Installable registry kept effect) ∧
    ¬ Nonempty (GeneralNominalCenteredHeadMatStepRefresh.Refresh installed refreshedContext) ∧
    ¬ Nonempty (GeneralNominalCenteredHeadMatStepRefresh.Refresh kept refreshedContext) :=
  ⟨checked,initial_source,point,coverage,control_trace,kept_model,r_pending,r_not_installable,
    no_redirected_refresh,no_redirected_refresh_kept⟩

end Yulang.GeneralNominalCenteredHeadMatRefreshRegression
