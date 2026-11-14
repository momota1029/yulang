import Yulang.GeneralNominalCenteredOriginFrameProduction

/-! Two coarse models agreeing on the original holes cannot assign different
types to an origin with one uniform finite value. This is a source-producer
falsifier; it imposes no new transition condition. -/
namespace Yulang.GeneralNominalCenteredOriginSeparation
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalLabelledOriginClosure GeneralNominalReadbackFunctionality
open GeneralNominalFiniteMeaning
open GeneralNominalScopedRecipeLabels
open GeneralNominalCenteredInstallObligations
open CommonNominalFullCarrier

theorem source_equal
    (value : Value models context origins remaining keys (.source target))
    (one : models first) (two : models last) (valuation : Nat → Ty)
    (firstLeaves : ∀ name ∈ remaining, At first .actual (origins name) (valuation name))
    (lastLeaves : ∀ name ∈ remaining, At last .actual (origins name) (valuation name)) :
    Equivalent (first target).1 (last target).1 := by
  have firstMeaning := GeneralNominalFrontierValuations.indexed_meaning value.labelled.2
    value.labelled.1.2.2 one (source_unique first target) valuation firstLeaves
  have lastMeaning := GeneralNominalFrontierValuations.indexed_meaning value.labelled.2
    value.labelled.1.2.2 two (source_unique last target) valuation lastLeaves
  have a := firstMeaning.2 _ (Observes.source target)
  have b := lastMeaning.2 _ (Observes.source target)
  exact ⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩

theorem no_value
    (one : models first) (two : models last) (valuation : Nat → Ty)
    (firstLeaves : ∀ name ∈ remaining, At first .actual (origins name) (valuation name))
    (lastLeaves : ∀ name ∈ remaining, At last .actual (origins name) (valuation name))
    (different : ¬ Equivalent (first target).1 (last target).1) :
    ¬ Nonempty (Value models context origins remaining keys (.source target)) := by
  rintro ⟨value⟩
  exact different (source_equal value one two valuation firstLeaves lastLeaves)

theorem no_origin_frame (job : Installation registry context root)
    (missing : ∀ facts,
      GeneralNominalCenteredSupport.Trusted job.after.erased job.after.sourceSites job.after.plans facts →
      GeneralNominalCenteredSupport.Fact.input job.plan ∉ facts) :
    ¬ NewlyRelevantOrigins registry context root := by
  intro produce
  obtain ⟨frame⟩ := produce job
  exact missing frame.facts frame.trusted frame.selected

/-- A finite value starts with a surviving source leaf or an allowed head. -/
theorem no_value_of_heads {model : GeneralNominalCommonBridge.Assignment} (valid : models model)
    (leaves : ∀ hole ∈ remaining, ¬ Same model target (origins hole))
    (heads : ∀ test ∈ tests, ¬ Head model target test) :
    ¬ ∃ value : Value models context origins remaining keys target, Vocabulary tests value.term := by
  rintro ⟨value,vocabulary⟩
  have known := value.labelled.2.1 model valid
  have closed := value.labelled.2.2
  cases term : value.term with
  | leaf hole =>
    rw [term] at known closed
    exact leaves hole (closed hole (List.mem_singleton_self _)) known
  | node test children =>
    rw [term] at known vocabulary
    exact heads test vocabulary.1 known.1

theorem no_frame_of_input (job : Installation registry context root)
    (model : GeneralNominalCommonBridge.Assignment)
    (before : GeneralNominalCenteredSteps.Models job.state model) (branch : job.plan.Holds model)
    (member : target ∈ GeneralNominalCenteredSourceInvariant.planInputs job.plan)
    (leaves : ∀ hole ∈ job.inventory.holes,
      ¬ Same model target (GeneralNominalCenteredSourceInvariant.origins context hole))
    (heads : ∀ test ∈ GeneralNominalCenteredSourceInvariant.testMenu context registry, ¬ Head model target test) :
    ¬ Nonempty (OriginFrame job job.inventory job.journal) := by
  rintro ⟨frame⟩
  have actual : GeneralNominalCenteredSteps.Models job.after model :=
    (GeneralNominalCenteredSteps.install_models job.enabled.1.2.1 model).mpr ⟨before,branch⟩
  have valid := GeneralNominalCenteredSourceTrace.trusted_models (.tail job.reachable job.step) frame.trusted actual
  apply no_value_of_heads valid leaves heads
  exact frame.inputs target (List.mem_flatMap.mpr ⟨.input job.plan,frame.selected,member⟩)

theorem no_preservation_of_child {roles : Roles.RoleDecls} {root : GeneralSourceDictionaries.Occurrence roles}
    (job : Installation registry context root)
    (model : GeneralNominalCommonBridge.Assignment)
    (before : GeneralNominalCenteredSteps.Models job.state model) (branch : job.plan.Holds model)
    (site : GeneralNominalCenters.Site roles) (member : site ∈ job.plan.emitted)
    (position : Fin (roles site.occurrence.demand.role).arity)
    (leaves : ∀ hole ∈ job.inventory.holes,
      ¬ Same model (.source (site.center position)) (GeneralNominalCenteredSourceInvariant.origins context hole))
    (heads : ∀ test ∈ GeneralNominalCenteredSourceInvariant.testMenu context registry,
      ¬ Head model (.source (site.center position)) test) :
    ¬ GeneralNominalCenteredSourceConstruction.NonterminalInstallPreservation registry context root := by
  intro produce
  obtain ⟨updated,growth,count,trace,next,⟨coverage⟩⟩ := produce job.state job.reachable
    job.inventory job.valid job.journal job.coverage job.plan job.support job.generated
    job.enabled job.novel job.guard job.children
  have actual : GeneralNominalCenteredSteps.Models job.after model :=
    (GeneralNominalCenteredSteps.install_models job.enabled.1.2.1 model).mpr ⟨before,branch⟩
  have valid := GeneralNominalCenteredSourceTrace.trusted_models
    (.tail job.reachable job.step) coverage.centeredTrusted actual
  obtain ⟨values,_,vocabulary⟩ := coverage.sites site (List.mem_append_right _ member)
  exact no_value_of_heads valid
    (fun hole present => leaves hole (GeneralNominalHoleElimination.trace_holes trace present))
    heads ⟨values position,vocabulary position⟩

end Yulang.GeneralNominalCenteredOriginSeparation
