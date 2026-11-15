import Yulang.GeneralDictionaryDefaultHeadEquationExtension214

/-! A corrected head extension can retain a supplied raw candidate branch.
Its existence is not inferred from Local or from journal satisfiability. -/
namespace Yulang.GeneralDictionaryDefaultRawBranch214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Use)
open GeneralNominalRecursiveInspection (Observes Finished)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalRootExtension184 (argument)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefaultConservative214 (lower_mem upper_mem candidate_origin nonpoint_binder_endpoints_separate)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

noncomputable def support (state : State roles) (candidate : Plan roles) (entries : Fin count → Use) :=
  GeneralDictionaryDefaultConservative214.support state candidate entries ++
    GeneralDictionaryDefaultPacketSupport213.headSources candidate

theorem current_head_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralDictionaryDefaultPacketSupport213.headSources candidate := by
  have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
    (GeneralDictionaryDefaultConfiguration209.seed (GeneralDictionaryDefaultTrace208.built_trace path))
  have low : GeneralDictionaryDefaultRawSeparation213.Low candidate.packet.context.state := by
    intro inv decl pur own pos hi present
    rw [seed,frame.context_eq] at present
    exact GeneralDictionaryDefaultRawSeparation213.current_separate source bound path hi present
  intro present
  rcases List.mem_append.mp present with privatePart | reportPart
  · have old := GeneralDictionaryDefaultRawSupport213.subset _ privatePart
    rw [← seed] at old
    exact GeneralDictionaryDefaultRawSeparation213.private_low candidate.packet
      (frame.registry_eq ▸ frame.visible) low invocation declaration purpose owner position high old
  · have old := GeneralNominalRawOrigin182.report_sources_subset
      candidate.packet.context candidate.packet.declaration candidate.packet.bounds reportPart
    rw [← seed] at old
    exact low invocation declaration purpose owner position high old

theorem nonpoint_head_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2) :
    candidate.binder name ∉ GeneralDictionaryDefaultPacketSupport213.headSources candidate := by
  rw [GeneralNominalBinderIdentity181.binder_fresh candidate name input nonpoint]
  have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
    (GeneralDictionaryDefaultConfiguration209.seed (GeneralDictionaryDefaultTrace208.built_trace path))
  rw [seed]
  exact current_head_separate source bound path candidate frame (by decide)

theorem branch_arguments_extension_iff (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (previous : Assignment) (valid : Models state previous)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds previous) :
    (∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ support state candidate entries, extended name = previous name) ∧
      ∀ i, (argument candidate (entries i)).Holds extended) ↔
    (∀ i, ∃ value, Observes previous (entries i).origin value) ∧
    (∀ i value, Observes previous (entries i).origin value →
      GeneralNominalCaptureMerges.Fits previous
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name) value) ∧
    (∀ i j first last, candidate.binder (entries i).name = candidate.binder (entries j).name →
      Observes previous (entries i).origin first → Observes previous (entries j).origin last → Equivalent first last) := by
  let P := fun m => Models state m ∧ GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry
    candidate.packet.context candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds m
  have linked : ∀ i, (argument candidate (entries i)).argument.endpoints.1 ∈ support state candidate entries ∧
      (argument candidate (entries i)).argument.endpoints.2 ∈ support state candidate entries ∧
      originSource (entries i).origin ∈ support state candidate entries := by
    intro i
    exact ⟨List.mem_append_left _ (List.mem_append_right _ (lower_mem candidate entries i)),
      List.mem_append_left _ (List.mem_append_right _ (upper_mem candidate entries i)),
      List.mem_append_left _ (List.mem_append_left _ (candidate_origin frame (entries i) (present i)))⟩
  rw [GeneralNominalPredicateExtension182.extension_iff P (support state candidate entries)
    (fun _ _ same held => ⟨(GeneralDictionaryDefaultJournalSupport213.models_iff state
      (fun name member => same name (List.mem_append_left _ (List.mem_append_left _ member)))).mp held.1,
      (GeneralDictionaryDefaultPacketSupport213.head_iff candidate
        (fun name member => same name (List.mem_append_right _ member))).mp held.2⟩)
    (fun i => argument candidate (entries i)) previous ⟨valid,branch⟩ linked]
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
        rcases List.mem_append.mp overlap with oldSupport | rawHead
        · rcases List.mem_append.mp oldSupport with old | endpoints
          · exact old
          · obtain ⟨entry,_,within⟩ := List.mem_flatMap.mp endpoints
            have separate := nonpoint_binder_endpoints_separate
              source bound path candidate frame.context_eq (entries i).name (input i) point entry.name
            simp only [List.mem_cons,List.not_mem_nil,or_false] at within
            exact False.elim (within.elim separate.1 separate.2)
        · exact False.elim (nonpoint_head_separate source bound path candidate frame
            (entries i).name (input i) point rawHead)
      have readback := GeneralDictionaryDefault214FullFreshness.candidate_overlap checked source bound path candidate
        frame (entries i) (present i) (actual i) (input i) point
        oldOverlap valid
      exact readback.2.2 value (previous (candidate.binder (entries i).name)).1 seen (.source _)

open GeneralDictionaryDefaultHeadEquationExtension214 (uses uses_mem uses_cover Compatible tests_frame)

theorem head_and_branch_extension_iff (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection candidate))
    (previous : Assignment) (valid : Models state previous)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds previous) :
    (∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = previous name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended) ↔ Compatible candidate previous := by
  have actual := fun i => GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate i)
  have notOutput := fun i => GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i)
  have extension := branch_arguments_extension_iff
    checked source bound path candidate frame (uses candidate)
    (uses_mem candidate) actual notOutput previous valid branch
  constructor
  · rintro ⟨extended,models,kept,input,captures,schema⟩
    have arguments : ∀ i, (argument candidate (uses candidate i)).Holds extended := by
      intro i
      refine ⟨captures _ (GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate i)),?_⟩
      simpa only [argument,actual i,ite_true] using schema.2 _ (uses_mem candidate i)
    exact ⟨fun test member => (tests_frame candidate frame previous extended
      (fun name member => kept name (List.mem_append_left _ member)) test member).mpr
      (schema.1 test member),extension.mp ⟨extended,models,kept,arguments⟩⟩
  · rintro ⟨tests,compatible⟩
    obtain ⟨extended,models,kept,arguments⟩ := extension.mpr compatible
    refine ⟨extended,models,kept,models.1.2.2.2.1 candidate.input frame.center_recorded,?_,?_,?_⟩
    · intro name named
      obtain ⟨origin,present⟩ := GeneralNominalHeadSchemaSemantic186.input_use candidate finished name named
      obtain ⟨index,equal⟩ := uses_cover candidate ⟨name,origin,.actual⟩ present
      have fits := (arguments index).1
      simpa only [argument,equal,Argument.Holds] using fits
    · intro test member
      exact (tests_frame candidate frame previous extended
      (fun name member => kept name (List.mem_append_left _ member)) test member).mp (tests test member)
    · intro entry present
      obtain ⟨index,equal⟩ := uses_cover candidate entry present
      have readback := (arguments index).2
      simpa only [argument,equal,GeneralNominalHeadSchemaNames186.head_actual candidate entry present,ite_true] using readback

end Yulang.GeneralDictionaryDefaultRawBranch214
