import Yulang.GeneralNominalCenteredSourceLiveConstruction
import Yulang.GeneralNominalCenteredOriginFrameProduction

/-! The source producer keeps retained meanings through ledger selection,
exposure and capture agreement. The remaining source statements are explicit;
their conditional composition constructs the strengthened installation case. -/
namespace Yulang.GeneralNominalCenteredSourceLiveProduction
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredSourceInvariant
open GeneralNominalCenteredSourceLiveReadbacks GeneralNominalCenteredInstallObligations
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels GeneralNominalRecursiveInspection
open GeneralNominalCenteredOriginFrameProduction (input_recorded)

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

structure OriginFrame' (job : Installation registry context root) (inventory : Inventory)
    (journal : Journal context root job.state.erased inventory) extends OriginFrame job inventory journal where
  retention : Retention registry context root job.after inventory.holes toOriginFrame.facts

theorem original_input (job : Installation registry context root)
    (retained : Retention registry context root job.state job.inventory.holes job.coverage.centeredFacts)
    (source : identity ∈ GeneralNominalState.sources context.state)
    (member : Origin.source identity ∈ planInputs job.plan) :
    ∃ value : Value
      (GeneralNominalCenteredSupport.Models job.state.erased job.state.sourceSites job.coverage.centeredFacts)
      context (origins context) job.inventory.holes (keyMenu registry) (.source identity),
      Vocabulary (testMenu context registry) value.term := by
  obtain ⟨model,valid,_⟩ := job.guard.2.2.2.2.2.2
  have read := FutureRead.candidate (root := root) job.plan job.guard.1 job.enabled member ⟨model,valid⟩
  exact ⟨retained.value identity source read,retained.vocabulary identity source read⟩

theorem frame_of_input (job : Installation registry context root)
    (retained : Retention registry context root job.state job.inventory.holes job.coverage.centeredFacts)
    (readback : GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites
      job.coverage.centeredFacts job.plan)
    (newInputs : OriginValues
      (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites (.input job.plan :: job.coverage.centeredFacts))
      context job.inventory.holes (keyMenu registry) (testMenu context registry) (planInputs job.plan)) :
    Nonempty (OriginFrame' job job.inventory job.journal) := by
  obtain ⟨support,recorded⟩ := input_recorded job
  have oldModels (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites
        (.input job.plan :: job.coverage.centeredFacts) model) :
      GeneralNominalCenteredSupport.Models job.state.erased job.state.sourceSites job.coverage.centeredFacts model := by
    have old := GeneralNominalCenteredOriginFrameProduction.models_subset
      (fun _ member => List.mem_cons_of_mem _ member) valid
    rw [GeneralNominalCenteredTrustedTransport.models_step job.step] at old
    exact old
  refine ⟨{
    identity := job.coverage.identity
    rawFacts := job.coverage.rawFacts
    rawReadbacks := job.coverage.rawReadbacks
    rawTrusted := GeneralNominalCenteredSourcePersistence.trusted_step job.step job.coverage.rawTrusted
    rawInputs := GeneralNominalCenteredSourcePersistence.trusted_inputs_step job.step job.coverage.rawInputs
    facts := .input job.plan :: job.coverage.centeredFacts
    trusted := GeneralNominalCenteredSupport.Trusted.input job.plan support
      (GeneralNominalCenteredTrustedTransport.trusted_step job.step job.coverage.centeredTrusted)
      (List.mem_cons_self ..) recorded ?_
    legacyIncluded := fun fact member => List.mem_cons_of_mem _ (job.coverage.legacyIncluded fact member)
    selected := List.mem_cons_self ..
    sites := fun site member => site_restrict (job.coverage.sites site member) oldModels
    inputs := ?_
    binders := origins_restrict job.coverage.binders oldModels
    retention := (retained.step job.step).strengthen (fun _ member => List.mem_cons_of_mem _ member) }⟩
  · intro slot visited test observation seen model valid
    apply readback slot visited test observation seen model
    rw [GeneralNominalCenteredTrustedTransport.models_step job.step] at valid
    exact valid
  · intro origin member
    rcases List.mem_append.mp member with here | earlier
    · exact newInputs origin here
    · exact origins_restrict job.coverage.inputs oldModels origin earlier

theorem finish {job : Installation registry context root} {inventory : Inventory}
    {journal : Journal context root job.state.erased inventory} (frame : OriginFrame' job inventory journal)
    (common : CommonCaptures frame.toOriginFrame) :
    ∃ next : Journal context root job.after.erased inventory,
      Nonempty (Coverage' registry context root job.after inventory next) := by
  obtain ⟨next,equal⟩ := GeneralNominalCompatibleJournalExtension.install_extension journal common.labels
    common.rootSame common.history job.plan.packet job.support (fun _ => ⟨common.presentation⟩)
  have constructors : job.plan.packet.context.state.constructors = context.state.constructors := by
    rw [job.enabled.1.2.1]
    exact (GeneralNominalCenteredSourceTrace.configuration_trace job.reachable).2.1
  have interpretation : job.plan.packet.context.interpretation = context.interpretation := by
    rw [job.enabled.1.2.1]
    exact (GeneralNominalCenteredSourceTrace.configuration_trace job.reachable).2.2
  refine ⟨next,⟨{
    identity := equal ▸ common.identity
    rawFacts := frame.rawFacts
    rawReadbacks := frame.rawReadbacks
    rawTrusted := frame.rawTrusted
    rawInputs := frame.rawInputs
    centeredFacts := frame.facts
    centeredTrusted := frame.trusted
    legacyIncluded := frame.legacyIncluded
    sites := ?_
    inputs := frame.inputs
    binders := frame.binders
    retention := frame.retention }⟩⟩
  intro site member
  change site ∈ job.state.sites ++ job.plan.emitted at member
  rcases List.mem_append.mp member with old | child
  · obtain ⟨values,same,vocab⟩ := frame.sites site old
    exact ⟨values,(congrFun equal site.occurrence).trans ((common.oldSites site old).trans same),vocab⟩
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp child
    exact GeneralNominalCenteredChildSourceValues.child_site job.state.erased.current job.enabled
      constructors interpretation (fun _ valid => valid.2.2 (.input job.plan) frame.selected)
      common.presentation.capture common.presentation.trees common.presentation.captureLabels common.scopes
      common.represented clause.val clause.property
      (job.plan.packet.checked.signature.2.2.2 clause.val clause.property) next.labels
      ((congrFun equal _).trans (common.presentation.children clause.val clause.property _))

def InputReadbackAndOrigins' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root,
    Retention registry context root job.state job.inventory.holes job.coverage.centeredFacts →
    GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites job.coverage.centeredFacts job.plan ∧
    OriginValues
      (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites (.input job.plan :: job.coverage.centeredFacts))
      context job.inventory.holes (keyMenu registry) (testMenu context registry) (planInputs job.plan)

def FullReportExposures' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root, ∀ _frame : OriginFrame' job job.inventory job.journal,
    ∃ updated operations, Changes context (keyMenu registry) job.inventory updated operations ∧
      ∃ journal : Journal context root job.state.erased updated,
        journal.labels = GeneralNominalCaptureFamilies.transformLabels operations job.journal.labels ∧
        ∃ refined : OriginFrame' job updated journal, IndividualHeadMatching refined.toOriginFrame

def CaptureReconciliation' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root, ∀ inventory,
    Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory →
    ∀ journal : Journal context root job.state.erased inventory,
    ∀ frame : OriginFrame' job inventory journal, IndividualHeadMatching frame.toOriginFrame →
      ∃ updated operations, Changes context (keyMenu registry) inventory updated operations ∧
        ∃ next : Journal context root job.state.erased updated,
          next.labels = GeneralNominalCaptureFamilies.transformLabels operations journal.labels ∧
          ∃ refined : OriginFrame' job updated next, Nonempty (CommonCaptures refined.toOriginFrame)

theorem nonterminal_install_of_three
    (inputs : InputReadbackAndOrigins' registry context root)
    (exposures : FullReportExposures' registry context root)
    (captures : CaptureReconciliation' registry context root) :
    GeneralNominalCenteredSourceLiveConstruction.NonterminalInstallPreservation' registry context root := by
  intro state reachable inventory valid journal coverage plan support generated enabled novel guard children
  let job : Installation registry context root :=
    ⟨state,reachable,inventory,valid,journal,coverage.toCoverage,plan,support,generated,enabled,novel,guard,children⟩
  obtain ⟨readback,newInputs⟩ := inputs job coverage.retention
  obtain ⟨frame⟩ := frame_of_input job coverage.retention readback newInputs
  obtain ⟨middle,operations,changes,middleJournal,_,refined,matched⟩ := exposures job frame
  obtain ⟨firstGrowth,trace⟩ := changes.trace
  obtain ⟨updated,lastOperations,lastChanges,next,_,finalFrame,⟨common⟩⟩ :=
    captures job middle (trace_valid trace valid) middleJournal refined matched
  obtain ⟨growth,tail⟩ := lastChanges.trace
  obtain ⟨afterJournal,coverageAfter⟩ := finish finalFrame common
  obtain ⟨combined,all⟩ := changes.prepend tail
  exact ⟨updated,combined,_,all,afterJournal,coverageAfter⟩

end Yulang.GeneralNominalCenteredSourceLiveProduction

