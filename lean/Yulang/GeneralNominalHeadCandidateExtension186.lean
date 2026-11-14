import Yulang.GeneralNominalHeadCandidateOverlap186
import Yulang.GeneralNominalRootExtension184
import Yulang.GeneralNominalPredicateExtension182

/-! Finite actual-head binder extension for a current candidate at any registered site.
Point captures use their exact bounds; nonpoint historical overlaps are derived. Endpoint/origin
linkage and simultaneous observation/bound/coherence tests remain explicit.
This is not a proof of candidate Joint or the general EvidenceNode field. -/
namespace Yulang.GeneralNominalHeadCandidateExtension186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalHeadLedgerFrame182 (fullSources)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

open GeneralNominalRootExtension184 (argument)

theorem candidate_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (argument candidate (entries i)).argument.endpoints.1 ∈ fullSources state ∧
      (argument candidate (entries i)).argument.endpoints.2 ∈ fullSources state ∧
      originSource (entries i).origin ∈ fullSources state) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (argument candidate (entries i)).Holds extended) ↔
    (∀ i, ∃ value, Observes previous (entries i).origin value) ∧
    (∀ i value, Observes previous (entries i).origin value →
      GeneralNominalCaptureMerges.Fits previous
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name) value) ∧
    (∀ i j first last, candidate.binder (entries i).name = candidate.binder (entries j).name →
      Observes previous (entries i).origin first → Observes previous (entries j).origin last → Equivalent first last) := by
  rw [GeneralNominalPredicateExtension182.extension_iff (Models state) (fullSources state)
    (fun _ _ same valid => (GeneralNominalHeadLedgerFrame182.models_iff state same).mp valid)
    (fun i => argument candidate (entries i)) previous valid linked]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨inhabited,bounds,coherent,_⟩
    exact ⟨inhabited,bounds,coherent⟩
  · rintro ⟨inhabited,bounds,coherent⟩
    refine ⟨inhabited,bounds,coherent,?_⟩
    intro i value overlap seen
    by_cases point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).2
    · have equal : candidate.binder (entries i).name =
          ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).1 := by
        simp only [Plan.binder, input i, ite_false, point, ite_true]
      change Equivalent value (previous (candidate.binder (entries i).name)).1
      rw [equal]
      have fits := bounds i value seen
      exact ⟨by simpa only [← point] using fits.2, fits.1⟩
    · have readback := GeneralNominalHeadCandidateOverlap186.candidate_overlap checked reachable candidate
        registered current visible (entries i) (present i) (actual i) (input i) point
        overlap previous valid
      exact readback.2.2 value (previous (candidate.binder (entries i).name)).1 seen (.source _)

end Yulang.GeneralNominalHeadCandidateExtension186
