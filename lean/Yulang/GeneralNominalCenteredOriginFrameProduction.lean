import Yulang.GeneralNominalCenteredInstallObligations

/-! The concrete origin-frame producer extends the actual trusted ledger.
Actual schema uses refer directly to their stored binder centers. The exact
snapshot readback needed by Trusted.input stays explicit. -/
namespace Yulang.GeneralNominalCenteredOriginFrameProduction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredSourceInvariant GeneralNominalCenteredInstallObligations
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}
variable {job : Installation registry context root} {inventory : Inventory}
variable {journal : Journal context root job.state.erased inventory}

theorem input_recorded (job : Installation registry context root) :
    ∃ support, GeneralNominalSupport.Fact.inputs job.plan.packet support ∈ job.after.erased.facts := by
  obtain ⟨support,member⟩ := GeneralNominalSupportChoices.alternatives_exists job.state.erased job.plan.packet job.support
    job.guard.2.1.1
  exact ⟨support,List.mem_append_left _ (List.mem_flatMap.mpr ⟨support,member,List.mem_cons_self ..⟩)⟩

theorem models_subset (included : first ⊆ last)
    (valid : GeneralNominalCenteredSupport.Models state roots last model) :
    GeneralNominalCenteredSupport.Models state roots first model :=
  ⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (included member)⟩

theorem frame_inputs (frame : OriginFrame job inventory journal)
    (valid : frame.models model) : GeneralNominalCenteredSupport.Inputs job.plan model :=
  valid.2.2 (.input job.plan) frame.selected

theorem frame_inhabited (frame : OriginFrame job inventory journal) :
    ∃ model, frame.models model := by
  obtain ⟨model,valid,branch⟩ := job.guard.2.2.2.2.2.2
  exact GeneralNominalCenteredSourceTrace.trusted_inhabited
    (.tail job.reachable job.step) frame.trusted
    ⟨model,(install_models job.enabled.1.2.1 model).mpr ⟨valid,branch⟩⟩

def actual_binder (frame : OriginFrame job inventory journal)
    (entry : GeneralNominalMaterialization.Use) (member : entry ∈ job.plan.headSchema.variables)
    (actual : entry.mode = .actual)
    (value : Value frame.models context (origins context) inventory.holes (keyMenu registry) entry.origin) :
    Value frame.models context (origins context) inventory.holes (keyMenu registry) (.source (job.plan.binder entry.name)) :=
  value.alias (fun model valid => by
    have same := (frame_inputs frame valid).2.2.2.1.2 entry member
    simpa only [actual,ite_true] using same)

theorem head_origin (frame : OriginFrame job inventory journal)
    (entry : GeneralNominalMaterialization.Use) (member : entry ∈ job.plan.headSchema.variables) :
    ∃ value : Value frame.models context (origins context) inventory.holes (keyMenu registry) entry.origin,
      Vocabulary (testMenu context registry) value.term := by
  apply frame.inputs
  exact List.mem_flatMap.mpr ⟨.input job.plan,frame.selected,
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨entry,member,rfl⟩))⟩

theorem needed_value (frame : OriginFrame job inventory journal)
    (needed : GeneralNominalSharedCaptures.Needed job.plan.packet name) :
    ∃ value : Value frame.models context (origins context) inventory.holes (keyMenu registry)
      (.source (job.plan.binder name)), Vocabulary (testMenu context registry) value.term := by
  obtain ⟨clause,member,used⟩ := needed
  apply frame.inputs
  exact List.mem_flatMap.mpr ⟨.input job.plan,frame.selected,
    List.mem_append_right _ (List.mem_map.mpr ⟨name,
      job.plan.packet.checked.scope.1 clause member name used,rfl⟩)⟩

theorem source_snapshot_readback {state : GeneralNominalSupport.Tracked roles} {plan : Plan roles}
    (same : plan.packet.context = state.source) :
    GeneralNominalCenteredSupport.Readback state roots facts plan := by
  intro slot visited test observation recorded model valid
  apply GeneralCanonicalObservations.recorded_sound plan.packet.context.state model
    (same.symm ▸ valid.1) (GeneralNominalSupport.head_recorded recorded)

theorem initial_snapshot_readback (job : Installation registry context root)
    (same : job.state = initial context root) :
    GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites job.coverage.centeredFacts job.plan := by
  apply source_snapshot_readback
  rw [job.enabled.1.2.1,same]
  rfl

theorem of_input (job : Installation registry context root)
    (readback : GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites
      job.coverage.centeredFacts job.plan)
    (newInputs : OriginValues
      (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites (.input job.plan :: job.coverage.centeredFacts))
      context job.inventory.holes (keyMenu registry) (testMenu context registry) (planInputs job.plan)) :
    Nonempty (OriginFrame job job.inventory job.journal) := by
  obtain ⟨support,recorded⟩ := input_recorded job
  have oldModels (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites
        (.input job.plan :: job.coverage.centeredFacts) model) :
      GeneralNominalCenteredSupport.Models job.state.erased job.state.sourceSites job.coverage.centeredFacts model := by
    have old := models_subset (fun _ member => List.mem_cons_of_mem _ member) valid
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
    binders := origins_restrict job.coverage.binders oldModels }⟩
  · intro slot visited test observation recorded model valid
    apply readback slot visited test observation recorded model
    rw [GeneralNominalCenteredTrustedTransport.models_step job.step] at valid
    exact valid
  · intro origin member
    rcases List.mem_append.mp member with here | earlier
    · exact newInputs origin here
    · exact origins_restrict job.coverage.inputs oldModels origin earlier

def InputReadbackAndOrigins (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root,
    GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites job.coverage.centeredFacts job.plan ∧
    OriginValues
      (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites (.input job.plan :: job.coverage.centeredFacts))
      context job.inventory.holes (keyMenu registry) (testMenu context registry) (planInputs job.plan)

theorem newly_relevant_origins (produce : InputReadbackAndOrigins registry context root) :
    NewlyRelevantOrigins registry context root := fun job => of_input job (produce job).1 (produce job).2

end Yulang.GeneralNominalCenteredOriginFrameProduction
