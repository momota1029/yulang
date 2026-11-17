import Yulang.GeneralDictionaryVersionedPointInstalledSelected233
import Yulang.GeneralNominalVersionedInstalledEvidenceAt233
set_option backward.isDefEq.respectTransparency false
/-! Modelwise literal EvidenceAt for terminal point installation. Unlike the
selection theorem, this needs no external selected fact or SafeKnown premise:
selection is used only when it is supplied by EvidenceAt's own antecedent. -/
namespace Yulang.GeneralDictionaryVersionedPointEvidenceAt233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPoint233
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
variable {state : State roles} {effect : Effect roles}
variable (allocated reserved ordinary)

theorem evidenceAt
    (registryEq : effect.registry = registry)
    (planEq : effect.plan = plan allocated reserved ordinary)
    (snapshot : effect.snapshot = state.core)
    (edges : state.core.erased.current.edges = [])
    (sites : ∀ site ∈ state.core.erased.current.sites, site.occurrence = root) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedBoundary232.boundary roles) registry
      (install state effect) root := by
  have terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [] := by
    rw [planEq]; exact children_empty allocated reserved ordinary
  have sameRoot : effect.plan.packet.site.occurrence = root := congrArg (fun p => p.packet.site.occurrence) planEq
  intro model valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  have same : demand = root := by
    rcases reached with same | reached
    · exact same
    · rw [← sameRoot] at reached
      exact (GeneralNominalVersionedInstalledEvidenceAt233.installed_generated_only terminal edges
        (fun site member => (sites site member).trans sameRoot.symm) reached).trans sameRoot
  subst demand
  have ourUnique := GeneralDictionaryVersionedPointInstalledSelected233.unique allocated reserved ordinary
    registryEq planEq snapshot valid
  have pair : key = declaration.id ∧ children = [] := by
    cases chosen with
    | ordinary _ chosen =>
      cases chosen with
      | ordinary _ chosen =>
        cases chosen with
        | selected _ unique _ => exact ourUnique.2 key children unique.1
  obtain ⟨rfl,rfl⟩ := pair
  cases childEvidence
  have evidence := GeneralNominalVersionedInstalledEvidence233.evidence snapshot terminal valid
  rw [registryEq,planEq] at evidence
  exact evidence

theorem source_evidenceAt
    (registryEq : effect.registry = registry)
    (planEq : effect.plan = plan allocated reserved ordinary)
    (snapshot : effect.snapshot = state.core)
    (edges : state.core.erased.current.edges = [])
    (sites : ∀ site ∈ state.core.erased.current.sites, site.occurrence = root) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) sourceRegistry
      (install state effect) root :=
  GeneralNominalVersionedSourceBoundary232.evidenceAt_iff.mpr
    (evidenceAt allocated reserved ordinary registryEq planEq snapshot edges sites)

end Yulang.GeneralDictionaryVersionedPointEvidenceAt233
