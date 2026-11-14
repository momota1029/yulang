import Yulang.GeneralNominalHeadCandidateOverlap186
import Yulang.GeneralNominalHeadCandidateSupport186
import Yulang.GeneralNominalRootExtension184
import Yulang.GeneralNominalPredicateExtension182

/-! Finite actual-head binder extension for a current candidate at any registered site.
Point captures use their exact bounds; nonpoint historical overlaps are derived. Origin linkage and endpoint separation are derived. Capture endpoints may be
new reservations outside the old journal, so they are explicitly preserved.
Only simultaneous observation/bound/coherence tests remain explicit.
This is not a proof of candidate Joint or the general EvidenceNode field. -/
namespace Yulang.GeneralNominalHeadConservativeExtension186
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

def captureEndpoints (candidate : Plan roles) (entries : Fin count → Use) : List Nat :=
  (List.ofFn entries).flatMap fun entry =>
    [((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1,
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2]

noncomputable def support (state : State roles) (candidate : Plan roles)
    (entries : Fin count → Use) : List Nat := fullSources state ++ captureEndpoints candidate entries

theorem lower_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).1 ∈
      captureEndpoints candidate entries :=
  List.mem_flatMap.mpr ⟨entries index,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem upper_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).2 ∈
      captureEndpoints candidate entries :=
  List.mem_flatMap.mpr ⟨entries index,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem conservative_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate entries, extended name = previous name) ∧
      ∀ i, (argument candidate (entries i)).Holds extended) ↔
    (∀ i, ∃ value, Observes previous (entries i).origin value) ∧
    (∀ i value, Observes previous (entries i).origin value →
      GeneralNominalCaptureMerges.Fits previous
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name) value) ∧
    (∀ i j first last, candidate.binder (entries i).name = candidate.binder (entries j).name →
      Observes previous (entries i).origin first → Observes previous (entries j).origin last → Equivalent first last) := by
  have linked : ∀ i, (argument candidate (entries i)).argument.endpoints.1 ∈ support state candidate entries ∧
      (argument candidate (entries i)).argument.endpoints.2 ∈ support state candidate entries ∧
      originSource (entries i).origin ∈ support state candidate entries := by
    intro i
    exact ⟨List.mem_append_right _ (lower_mem candidate entries i),
      List.mem_append_right _ (upper_mem candidate entries i),
      List.mem_append_left _ (GeneralNominalHeadCandidateSupport186.candidate_origin
        state candidate registered aligned (entries i) (present i))⟩
  rw [GeneralNominalPredicateExtension182.extension_iff (Models state) (support state candidate entries)
    (fun _ _ same valid => (GeneralNominalHeadLedgerFrame182.models_iff state
      (fun name member => same name (List.mem_append_left _ member))).mp valid)
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
    · have oldOverlap : candidate.binder (entries i).name ∈ fullSources state := by
        rcases List.mem_append.mp overlap with old | endpoints
        · exact old
        · obtain ⟨entry,_,within⟩ := List.mem_flatMap.mp endpoints
          have separate := GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate
            reachable candidate current (entries i).name (input i) point entry.name
          simp only [List.mem_cons,List.not_mem_nil,or_false] at within
          exact False.elim (within.elim separate.1 separate.2)
      have readback := GeneralNominalHeadCandidateOverlap186.candidate_overlap checked reachable candidate
        registered current visible (entries i) (present i) (actual i) (input i) point
        oldOverlap previous valid
      exact readback.2.2 value (previous (candidate.binder (entries i).name)).1 seen (.source _)

end Yulang.GeneralNominalHeadConservativeExtension186
