import Yulang.GeneralNominalCenteredSourceRefreshWitness
import Yulang.GeneralNominalCenteredSourceSnapshotLedger
import Yulang.GeneralNominalCenteredSourceLiveChecks

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredSourceLedgerObstruction
open GeneralNominalCenteredSourceRefreshWitness
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)

theorem recorded_facts : refreshed.erased.facts =
    [.inputs packetP [], .outputs packetP []] := by
  change GeneralNominalSupportChoices.installedFacts initialState.erased packetP ++ [] = _
  rw [GeneralNominalSupportChoices.empty_alternatives initialState.erased packetP rfl source_guardP]
  rfl

theorem no_discharge (focus : Occurrence roles) :
    ¬ GeneralNominalSupport.Discharged refreshed.erased.current focus := by
  intro discharged
  induction discharged with
  | packet packet member children ih =>
      have same : packet = packetP := List.mem_singleton.mp member
      subst packet
      exact ih emittedChild.occurrence (childrenP_exact ▸ List.mem_singleton_self _)
  | alias first last one two same discharged ih => exact ih

theorem no_settled_packet (packet : GeneralNominalSaturationState.Packet roles) :
    ¬ GeneralNominalSettledSupport.PacketSettled refreshed.erased.current packet := by
  intro settled
  exact no_discharge packet.site.occurrence
    (GeneralNominalSettledSupport.packet_settled_demand settled)

theorem no_merge_fact (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) :
    GeneralNominalSupport.Fact.merge first last support ∉ refreshed.erased.facts := by
  rw [recorded_facts]
  simp

theorem raw_trusted_source_models
    (trusted : GeneralNominalSettledSupport.Trusted refreshed.erased facts)
    (model : Assignment) (sourceValid : GeneralNominalState.Models source model) :
    GeneralNominalSettledSupport.Models refreshed.erased facts model := by
  refine ⟨sourceValid,?_⟩
  induction trusted with
  | source => intro fact member; cases member
  | input packet support prior member readback ih =>
      rw [recorded_facts] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same | impossible
      · cases same
        intro fact present
        rcases List.mem_cons.mp present with rfl | present
        · exact inputsP model
        · exact ih fact present
      · cases impossible
  | output packet support prior member included settled ih =>
      exact False.elim (no_settled_packet packet settled)
  | merge first last support prior member evidence ih =>
      exact False.elim (no_merge_fact first last support member)

theorem shared_trusted_source_models
    (trusted : GeneralNominalSharedSupport.Trusted refreshed.erased facts readbacks)
    (model : Assignment) (sourceValid : GeneralNominalState.Models source model) :
    GeneralNominalSharedSupport.Models refreshed.erased facts model :=
  raw_trusted_source_models (GeneralNominalSharedSupport.trusted_old trusted) model sourceValid

theorem centered_trusted_source_models
    (trusted : GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts)
    (model : Assignment) (sourceValid : GeneralNominalState.Models source model) :
    GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites facts model := by
  refine ⟨sourceValid,?_,?_⟩
  · intro site member
    cases List.mem_singleton.mp member
    exact GeneralNominalCenters.point_root_holds source.seed root (fun _ => rfl) model
  · induction trusted with
    | source => intro fact member; cases member
    | legacy facts readbacks prior =>
        intro fact member
        obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
        exact (shared_trusted_source_models prior model sourceValid).2 raw present
    | input plan support prior member recorded readback ih =>
        have same : plan = planP := List.mem_singleton.mp member
        subst plan
        intro fact present
        rcases List.mem_cons.mp present with rfl | present
        · exact centered_inputsP model sourceValid
        · exact ih fact present
    | output plan support prior member recorded included settled ih =>
        exact False.elim (no_settled_packet plan.packet settled)
    | merge first last support prior recorded holds same ih =>
        exact False.elim (no_merge_fact first.observed last.observed support recorded)

theorem bad_every_trusted
    (trusted : GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts) :
    GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites facts bad :=
  centered_trusted_source_models trusted bad bad_source

theorem no_trusted_readbackR
    (trusted : GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts) :
    ¬ GeneralNominalCenteredSupport.Readback refreshed.erased refreshed.sourceSites facts planR := by
  intro readback
  have member : (1 : Fin refreshedSource.base.slots) ∈ GeneralNominalSupport.readsMany refreshedSource
      (GeneralNominalInspection.queries refreshedSource interpretation r) [(1,1)] := by
    rw [readsR]
    exact List.mem_cons_self ..
  exact current_headR_not_source (readback 1 member _ _ current_headR bad (bad_every_trusted trusted))

theorem no_trusted_exact_observation :
    ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
      ∀ model, GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites facts model →
        (GeneralCanonicalObservations.Observation.normalized refreshedBase 1 (.pair (.var 4) (.var 4))).Holds model := by
  rintro ⟨facts,trusted,exactObservation⟩
  exact current_headR_not_source (exactObservation bad (bad_every_trusted trusted))

open GeneralNominalCenteredSteps GeneralNominalCenteredSourceSnapshotLedger
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination

theorem no_settled_after_install (packet : GeneralNominalSaturationState.Packet roles) :
    ¬ GeneralNominalSettledSupport.PacketSettled afterP.erased.current packet :=
  fun settled => no_settled_packet packet
    (GeneralNominalCenteredSourcePersistence.settled_step refreshStep settled)

theorem no_complete_ledger_after_install :
    ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted afterP.erased afterP.sourceSites afterP.plans facts ∧
      LedgerComplete afterP facts := by
  rintro ⟨facts,trusted,complete⟩
  exact no_settled_after_install packetP (complete.settled trusted (List.mem_cons_self ..))

theorem no_complete_ledger :
    ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
      LedgerComplete refreshed facts := by
  rintro ⟨facts,trusted,complete⟩
  exact no_settled_packet packetP (complete.settled trusted (List.mem_cons_self ..))

theorem empty_ledger_incomplete : ¬ LedgerComplete refreshed [] := by
  intro complete
  exact List.not_mem_nil ((complete.1 planP (List.mem_cons_self ..)).1)

theorem no_snapshot_ledger :
    ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
      SnapshotReadbacks refreshed facts := by
  rintro ⟨facts,trusted,sound⟩
  exact no_trusted_readbackR trusted (sound.readback (plan := planR) rfl)

theorem empty_ledger_not_snapshot : ¬ SnapshotReadbacks refreshed [] :=
  fun sound => no_snapshot_ledger ⟨[],.source,sound⟩

theorem no_snapshot_coverage (inventory : Inventory)
    (journal : Journal context root refreshed.erased inventory) :
    ¬ Nonempty (Coverage'' registry context root refreshed inventory journal) := by
  rintro ⟨coverage⟩
  exact no_snapshot_ledger ⟨coverage.centeredFacts,coverage.centeredTrusted,coverage.snapshot⟩

theorem previous_inventory_excluded :
    ¬ Nonempty (Coverage'' GeneralNominalCenteredInstallExample.registry
      GeneralNominalCenteredInstallExample.context GeneralNominalCenteredInstallExample.root
      GeneralNominalCenteredInstallCounterexample.job.state GeneralNominalCenteredInstallCounterexample.job.inventory
      GeneralNominalCenteredInstallCounterexample.job.journal) := by
  rintro ⟨coverage⟩
  exact GeneralNominalCenteredSourceLiveChecks.old_job_excluded ⟨coverage.toCoverage'⟩

theorem head_before_refresh
    (seen : GeneralNominalSupport.Head afterP.erased.current.context.state identity test observation) :
    GeneralNominalSupport.Head source identity test observation := by
  cases seen with
  | scalar slot base recorded => exact .scalar (snapshot := source) slot base recorded
  | structural slot kind children recorded => exact .structural (snapshot := source) slot kind children recorded
  | nominal slot descriptor recorded => exact .nominal (snapshot := source) slot descriptor recorded

theorem snapshot_before_refresh : SnapshotReadbacks afterP [] := by
  intro identity test observation seen model valid
  exact GeneralCanonicalObservations.recorded_sound source model valid.1
    (GeneralNominalSupport.head_recorded (head_before_refresh seen))

theorem refresh_preservation_counterexample :
    GeneralNominalCenteredSupport.Trusted afterP.erased afterP.sourceSites afterP.plans [] ∧
      SnapshotReadbacks afterP [] ∧ Step registry root afterP refreshed ∧
      ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
        SnapshotReadbacks refreshed facts :=
  ⟨.source,snapshot_before_refresh,refreshStep,no_snapshot_ledger⟩

theorem no_executable_readbacks : ¬ ExecutableReadbacks registry root refreshed := by
  intro produce
  obtain ⟨facts,trusted,readback⟩ := produce planR [] generatedR enabledR novelR guardR (by decide +kernel)
  exact no_trusted_readbackR trusted readback

theorem no_preserved_exact_input_invariant (invariant : State roles → Prop)
    (started : invariant initialState)
    (preserved : ∀ before after, invariant before → Step registry root before after → invariant after)
    (inputs : ∀ state, invariant state → ExecutableReadbacks registry root state) : False := by
  have reached : ∀ state, B4Target.Steps (Step registry root) initialState state → invariant state := by
    intro state path
    induction path with
    | refl => exact started
    | tail path step ih => exact preserved _ _ ih step
  exact no_executable_readbacks (inputs refreshed (reached refreshed refreshed_reachable))

theorem unknown_input : ¬ GeneralNominalState.Known source 2 := by
  rintro ⟨slot,equal,known⟩
  have same : slot = (2 : Fin 4) := Fin.ext equal
  subst slot
  rcases known with impossible | ⟨descriptor,recorded⟩
  · exact impossible rfl
  · cases recorded

theorem counterexample :
    GeneralDeclarations.Checked registry ∧
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧ ¬ GeneralNominalState.Known source 2 ∧
      B4Target.Steps (Step registry root) initialState refreshed ∧ Step registry root refreshed afterR ∧
      ¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
        GeneralNominalCenteredSupport.Readback refreshed.erased refreshed.sourceSites facts planR := by
  refine ⟨checked,initial_source,point,unknown_input,refreshed_reachable,stepR,?_⟩
  rintro ⟨facts,trusted,readback⟩
  exact no_trusted_readbackR trusted readback

end Yulang.GeneralNominalCenteredSourceLedgerObstruction
