import Yulang.GeneralNominalRootOverlap184
import Yulang.GeneralNominalPredicateExtension182

/-! Finite actual-head binder extension for a current root candidate.
Reachable historical overlaps are discharged, not assumed. Endpoint/origin
linkage and simultaneous observation/bound/coherence tests remain explicit.
This is not a proof of candidate Joint or the general EvidenceNode field. -/
namespace Yulang.GeneralNominalRootExtension184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalModeLedger181 (fullSources)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def argument (candidate : Plan roles) (entry : Use) : NominalArgument :=
  ⟨⟨(GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name,
    candidate.binder entry.name⟩,entry.origin⟩

theorem root_extension_iff (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ∀ i, ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).2)
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
    (fun _ _ same => GeneralNominalModeLedger181.centered_models_frame state same)
    (fun i => argument candidate (entries i)) previous valid linked]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨inhabited,bounds,coherent,_⟩
    exact ⟨inhabited,bounds,coherent⟩
  · rintro ⟨inhabited,bounds,coherent⟩
    refine ⟨inhabited,bounds,coherent,?_⟩
    intro i value overlap seen
    have readback := GeneralNominalRootOverlap184.candidate_root_overlap checked reachable candidate
      registered atRoot current visible (entries i) (present i) (actual i) (input i) (nonpoint i)
      overlap previous valid
    exact readback.2.2 value (previous (candidate.binder (entries i).name)).1 seen (.source _)

end Yulang.GeneralNominalRootExtension184
