import Yulang.GeneralNominalGroundProvenance182
import Yulang.GeneralNominalSupportProvenance182
import Yulang.GeneralNominalPredicateExtension182

/-! Uniform historical witnesses and exact residual origin agreement for I30.
The overlap provenance and candidate agreement are explicit, not produced by
capture bounds. The unrestricted EvidenceNode remains outside these results. -/
namespace Yulang.GeneralNominalOriginAgreement183
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same same_trans same_symm)
open GeneralNominalSupportProvenance182 (ActualBinder actual_same)
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalModeLedger181 (fullSources)
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

/-- A single historical producer is selected independently of the model. -/
theorem uniform_site_fits
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ plan ∈ state.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index ∧
      ∀ model, Models state model → GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
        (model (site.center index)).1 := by
  obtain ⟨plan,registered,name,needed,equal⟩ :=
    GeneralNominalGroundProvenance182.site_needed reachable site member index center
  refine ⟨plan,registered,name,needed,equal,?_⟩
  intro model valid
  rw [← equal]
  exact GeneralNominalRegisteredReadback182.registered_capture_fits plan registered valid name (Or.inr needed)

theorem source_agreement_iff (source : ActualBinder state name historical)
    (valid : Models state model) :
    Same model candidate (.source name) ↔ Same model candidate historical := by
  have recorded := actual_same valid source
  exact ⟨fun equal => same_trans equal (same_symm recorded),fun equal => same_trans equal recorded⟩

theorem actual_origins_agree (first : ActualBinder state name one)
    (last : ActualBinder state name two) (valid : Models state model) :
    Same model one two :=
  same_trans (actual_same valid first) (same_symm (actual_same valid last))

theorem uniform_source_agreement_iff (source : ActualBinder state name historical) :
    (∀ model, Models state model → Same model candidate (.source name)) ↔
    (∀ model, Models state model → Same model candidate historical) :=
  ⟨fun agrees model valid => (source_agreement_iff source valid).mp (agrees model valid),
   fun agrees model valid => (source_agreement_iff source valid).mpr (agrees model valid)⟩

/-- The observation-existence conjunct is necessary: an unobserved candidate
cannot acquire Same merely from a vacuous readback implication. -/
theorem readback_agreement_iff (source : ActualBinder state name historical)
    (valid : Models state model) :
    ((∃ value, Observes model candidate value) ∧
      ∀ value, Observes model candidate value → Equivalent value (model name).1) ↔
    Same model candidate historical := by
  rw [← source_agreement_iff source valid]
  constructor
  · rintro ⟨inhabited,readback⟩
    refine ⟨inhabited,⟨_,.source _⟩,?_⟩
    intro value other seen named
    cases named
    exact readback value seen
  · intro equal
    exact ⟨equal.1,fun value seen => equal.2.2 value (model name).1 seen (.source _)⟩

/-- Exact finite conservative extension criterion with historical origin
agreement. The ActualBinder provenance of overlapping centers is explicit. -/
theorem extension_iff_historical (arguments : Fin count → NominalArgument)
    (historical : Fin count → Origin) (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state)
    (provenance : ∀ i, (arguments i).argument.center ∈ fullSources state →
      ActualBinder state (arguments i).argument.center (historical i)) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last →
      Equivalent first last) ∧
    (∀ i, (arguments i).argument.center ∈ fullSources state →
      Same previous (arguments i).origin (historical i)) := by
  rw [GeneralNominalPredicateExtension182.extension_iff (Models state) (fullSources state)
    (fun _ _ same valid => GeneralNominalModeLedger181.centered_models_frame state same valid)
    arguments previous valid linked]
  constructor
  · rintro ⟨inhabited,bounds,coherent,overlap⟩
    refine ⟨inhabited,bounds,coherent,?_⟩
    intro i member
    exact (readback_agreement_iff (provenance i member) valid).mp
      ⟨inhabited i,fun value seen => overlap i value member seen⟩
  · rintro ⟨inhabited,bounds,coherent,agreement⟩
    refine ⟨inhabited,bounds,coherent,?_⟩
    intro i value member seen
    exact ((readback_agreement_iff (provenance i member) valid).mpr (agreement i member)).2 value seen

end Yulang.GeneralNominalOriginAgreement183
