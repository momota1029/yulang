import Yulang.GeneralNominalRootExtension184
import Yulang.GeneralDictionaryDefaultJournalSupport213
import Yulang.GeneralDictionaryDefault214FullFreshness
import Yulang.GeneralDictionaryDefaultCandidateActual214
import Yulang.GeneralNominalHeadCandidateSupport186
import Yulang.GeneralNominalPredicateExtension182

/-! Support facts for finite actual-head extensions in the corrected journal.
Current candidate capture endpoints are retained even when newly allocated. -/
namespace Yulang.GeneralDictionaryDefaultConservative214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRootExtension184 (argument)
open GeneralNominalMaterialization (Use)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def captureEndpoints (candidate : Plan roles) (entries : Fin count → Use) : List Nat :=
  (List.ofFn entries).flatMap fun entry =>
    [((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1,
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2]

noncomputable def support (state : State roles) (candidate : Plan roles)
    (entries : Fin count → Use) : List Nat := journalSources state ++ captureEndpoints candidate entries

theorem lower_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).1 ∈
      captureEndpoints candidate entries :=
  List.mem_flatMap.mpr ⟨entries index,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem upper_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).2 ∈
      captureEndpoints candidate entries :=
  List.mem_flatMap.mpr ⟨entries index,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem registered_center (state : State roles) (site : Site roles)
    (registered : site ∈ state.core.sites) (member : name ∈ List.ofFn site.center) :
    name ∈ journalSources state := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  have inside : site.center index ∈ GeneralNominalCenteredFrame179.siteSources site :=
    List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩
  have ledger := List.mem_flatMap.mpr ⟨site,registered,inside⟩
  simp only [journalSources,List.mem_append]
  exact Or.inl (Or.inl (Or.inr ledger))

theorem candidate_origin {state : State roles}
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) :
    originSource entry.origin ∈ journalSources state := by
  apply registered_center state candidate.input frame.center_recorded
  apply (GeneralNominalHeadCandidateSupport186.head_roots candidate ?_).2 entry present
  exact frame.role_eq.trans (congrArg (fun root : Occurrence roles => root.demand.role)
    (candidate.input_exact.trans frame.occurrence_eq)).symm

theorem current_capture_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles)
    (current : packet.context = state.core.erased.current.context)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  have seed : packet.context.state.seed = context.state.seed :=
    (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) current).trans
      (GeneralDictionaryDefaultConfiguration209.seed (GeneralDictionaryDefaultTrace208.built_trace path))
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [seed,current]
    exact GeneralDictionaryDefaultRawSeparation213.current_separate source bound path high
  simpa only [seed] using GeneralNominalRawSupport183.capture_inputs_separate packet high outside name

theorem nonpoint_binder_endpoints_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (other : Nat) :
    candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).1 ∧
      candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).2 := by
  rw [GeneralNominalBinderIdentity181.binder_fresh candidate name input nonpoint]
  have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) current).trans
    (GeneralDictionaryDefaultConfiguration209.seed (GeneralDictionaryDefaultTrace208.built_trace path))
  rw [seed]
  exact current_capture_separate source bound path candidate.packet current (by decide) other
theorem conservative_extension_iff (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
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
      List.mem_append_left _ (candidate_origin frame (entries i) (present i))⟩
  rw [GeneralNominalPredicateExtension182.extension_iff (Models state) (support state candidate entries)
    (fun _ _ same valid => (GeneralDictionaryDefaultJournalSupport213.models_iff state
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
    · have oldOverlap : candidate.binder (entries i).name ∈ journalSources state := by
        rcases List.mem_append.mp overlap with old | endpoints
        · exact old
        · obtain ⟨entry,_,within⟩ := List.mem_flatMap.mp endpoints
          have separate := nonpoint_binder_endpoints_separate
            source bound path candidate frame.context_eq (entries i).name (input i) point entry.name
          simp only [List.mem_cons,List.not_mem_nil,or_false] at within
          exact False.elim (within.elim separate.1 separate.2)
      have readback := GeneralDictionaryDefault214FullFreshness.candidate_overlap checked source bound path candidate
        frame (entries i) (present i) (actual i) (input i) point
        oldOverlap valid
      exact readback.2.2 value (previous (candidate.binder (entries i).name)).1 seen (.source _)

end Yulang.GeneralDictionaryDefaultConservative214
