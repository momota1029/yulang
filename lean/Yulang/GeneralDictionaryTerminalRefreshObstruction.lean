import Yulang.GeneralDictionarySettledTerminalPrefix
/-! Design: the actual settled Container output still equals an unresolved
source. Two models of the installed state give it different outer heads.
Therefore a model-preserving refresh cannot make this output Known.
This concerns this concrete legacy settled prefix, not global incompleteness
of SharedSteps or a claim that a generated consumer has been constructed. -/
namespace Yulang.GeneralDictionaryTerminalRefreshObstruction
open CommonNominalFullCarrier GeneralNominalSupportSiblings
open GeneralNominalDownstreamSiblingFixture GeneralNominalSaturationState
open GeneralNominalSupport
private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem int_not_shape (shape : GeneralNormalizedObservation.Shape)
    (children : Fin shape.arity → Fin slots)
    (assignment : Fin slots → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
    ¬ Subtype (.base .int) ((shape.term children).eval CommonNominalFullCarrier.model assignment) := by
  intro below
  let role : CommonNominalFullDemand.Head := match shape with
    | .pair => .pair | .variant tag => .variant tag | _ => .records
  have probe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => [role]⟩ (.role 0)
  cases shape with
  | pair | variant | exactEmpty =>
    simp [role, GeneralNormalizedObservation.Shape.term,Core.PresenceGeneration.TyTerm.eval,
      CommonNominalFullCarrier.model,CommonNominalFullCarrier.pair,CommonNominalFullCarrier.variant,observeTy,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe
  | record labels =>
    cases labels <;>
      simp [role, GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,List.ofFn_succ,
        Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,CommonNominalFullCarrier.record,
        observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
        CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe


theorem int_model : Models GeneralNominalBudgetContainer.afterC.current
    (GeneralNominalOutputGrowth.finiteModel 1) := by
  let model := GeneralNominalOutputGrowth.finiteModel 1
  have valid := (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1)
  have outputs : GeneralNominalPacketSupport.Outputs cutContainer model :=
    cut_journal_facts (.outputs cutContainer []) (by simp [cutJournal])
      (by
        simp only [Fact.dependencies,List.mem_singleton]
        intro same
        have ids := congrArg GeneralSourceDictionaries.Occurrence.identity same
        exact (by decide +kernel : kidW.identity ≠ kidC.identity) ids)
  exact (GeneralNominalFeedbackSites.install_models afterP.current containerPacket
    (GeneralNominalFeedbackSites.emitted containerPacket) rfl model).mpr
      ⟨GeneralNominalBudgetContainer.source_model model valid,
       GeneralNominalBudgetContainer.branch model valid outputs⟩

theorem nominal_model : Models GeneralNominalBudgetContainer.afterC.current journalModel :=
  (GeneralNominalFeedbackSites.install_models afterP.current containerPacket
    (GeneralNominalFeedbackSites.emitted containerPacket) rfl journalModel).mpr
      ⟨GeneralNominalBudgetContainer.source_model journalModel cut_journal_models.1,
       GeneralNominalBudgetContainer.journal_branch⟩

theorem int_output : (GeneralNominalOutputGrowth.finiteModel 1 out).1 = .base .int := by
  have above := GeneralDictionarySettledTerminalPrefix.output_above_slots
  have zero : 2-out = 0 := by omega
  simp [GeneralNominalOutputGrowth.finiteModel,zero,GeneralNominalOutputGrowth.tower]; rfl

theorem nominal_output : (journalModel out).1 = nominal 0 [.inl (.base .int)] := by
  simp [journalModel,GeneralNominalOutputGrowth.tower]; rfl

/-- Even adding slots cannot soundly choose an outer head for this output. -/
theorem no_known (state : GeneralNominalState.State)
    (one : GeneralNominalState.Models state (GeneralNominalOutputGrowth.finiteModel 1))
    (two : GeneralNominalState.Models state journalModel) :
    ¬ GeneralNominalState.Known state out := by
  rintro ⟨slot,source,head | ⟨descriptor,recorded⟩⟩
  · have seen1 := GeneralNominalState.normalized_models state _ one
    have seen2 := GeneralNominalState.normalized_models state _ two
    cases equation : state.view.heads slot with
    | deferred reason => exact head (by simp [GeneralNormalizedObservation.Snapshot.graph,equation,GeneralNormalizedObservation.Head.node])
    | scalar base =>
      have a := seen1 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have b := seen2 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have x : Equivalent (.base .int) (.base base) := by
        simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,int_output] using a
      have y : Equivalent (nominal 0 [.inl (.base .int)]) (.base base) := by
        simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,nominal_output] using b
      exact int_not_nominal _ _ (subtype_trans x.1 y.2)
    | structural kind children =>
      have a := seen1 slot ((state.view.shapes kind).term children) (by simp [equation,GeneralNormalizedObservation.Head.term])
      exact int_not_shape _ children _ (by simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,int_output] using a.1)
  · obtain ⟨values,_,equal⟩ := one.2.1 slot descriptor recorded
    exact int_not_nominal _ _ (by simpa [GeneralNominalState.Denotes,source,int_output] using equal.1)

/-- Exact refresh preserves both models and therefore cannot expose this head. -/
theorem refresh_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh GeneralNominalBudgetContainer.afterC.current next) :
    ¬ GeneralNominalState.Known next.state out :=
  no_known next.state (certificate.exact _ int_model) (certificate.exact _ nominal_model)

private theorem head_known (head : Head snapshot identity test observation) :
    GeneralNominalState.Known snapshot identity := by
  cases head with
  | scalar slot base seen =>
    exact ⟨slot,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node])⟩
  | structural slot kind children seen =>
    exact ⟨slot,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node])⟩
  | nominal slot descriptor seen => exact ⟨slot,rfl,Or.inr ⟨descriptor,seen⟩⟩

theorem refresh_not_ready (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh GeneralNominalBudgetContainer.afterC.current next) :
    ¬ GeneralNominalSettledSupport.ReadyAt
      {GeneralNominalBudgetContainer.afterC with current :=
        {GeneralNominalBudgetContainer.afterC.current with context := next}} out := by
  rintro ⟨test,observation,head,_⟩
  exact refresh_unknown next certificate (head_known head)

end Yulang.GeneralDictionaryTerminalRefreshObstruction
