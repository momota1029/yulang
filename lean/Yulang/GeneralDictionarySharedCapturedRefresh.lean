import Yulang.GeneralDictionarySharedCapturedInstallation
import Yulang.GeneralNominalOutputGrowthRefresh

/-! A source-preserving fresh-slot snapshot for the captured producer. -/
namespace Yulang.GeneralDictionarySharedCapturedRefresh
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedInstallation
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)

private theorem nominal_congr (a b : Ty) (eq : Equivalent a b) :
    Equivalent (nominal 0 [.inl a]) (nominal 0 [.inl b]) := by
  constructor
  all_goals
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro i x y one two
    have zero : i = 0 := by
      have h := (List.getElem?_eq_some_iff.mp one).1
      simp only [List.length_cons,List.length_nil] at h
      omega
    subst i
    cases one; cases two
  · exact eq
  · exact ⟨eq.2,eq.1⟩

/-- Shape tests and the actual variable use together determine a point
nominal descriptor; the finite witness is not used here. -/
theorem endpoint_equation (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current assignment) (endpoint : Nat) (which : endpoint = lo ∨ endpoint = hi) :
    Equivalent (assignment endpoint).1 (nominal 0 [.inl (assignment 2).1]) := by
  have parent := valid.2.1 packet (by simp [after,GeneralNominalSharedSteps.install,GeneralNominalFeedbackSites.install])
  have shape : Test.Holds (.nominal 0 1) (assignment endpoint).1 := by
    rcases which with rfl | rfl
    · exact (producer_shape assignment valid).1
    · exact (producer_shape assignment valid).2
  have use : (⟨0,.nominal (.source endpoint) 0 0,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.namedSchema packet).variables := by
    rw [schema_exact]
    rcases which with rfl | rfl <;> simp
  obtain ⟨actual,seen⟩ := (parent.2.2.2.1 _ use).1
  have same := GeneralNominalSharedCaptures.point_use parent.2.2 use rfl
    (by simp [Declaration.outputNames]) capture_input
  have actualEq := same.2.2 actual (assignment 2).1 seen (.source 2)
  obtain ⟨args,size,equal⟩ := shape
  cases seen with
  | nominal previous observed found =>
    cases previous
    have invariant := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 observed.1)
    cases args with
    | nil => cases size
    | cons first tail =>
      have tailNil : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
      subst tail
      have compared := invariant.2.2 0 first (.inl actual) rfl found
      cases first with
      | inr => cases compared
      | inl original =>
        have lifted := nominal_congr original (assignment 2).1
          ⟨subtype_trans compared.1 actualEq.1,subtype_trans actualEq.2 compared.2⟩
        exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩

theorem lo_ne_hi : lo ≠ hi := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity source registry root.identity _ _).mp equal
  cases same

abbrev identifiers (slot : Fin 5) : Nat := if slot.val = 3 then lo else if slot.val = 4 then hi else slot.val

theorem identifiers_injective : Function.Injective identifiers := by
  intro first last equal
  have one : first.val=0 ∨ first.val=1 ∨ first.val=2 ∨ first.val=3 ∨ first.val=4 := by omega
  have two : last.val=0 ∨ last.val=1 ∨ last.val=2 ∨ last.val=3 ∨ last.val=4 := by omega
  have l0 := lo_fresh 0 (by omega); have l1 := lo_fresh 1 (by omega); have l2 := lo_fresh 2 (by omega)
  have h0 := hi_fresh 0 (by omega); have h1 := hi_fresh 1 (by omega); have h2 := hi_fresh 2 (by omega)
  have lh := lo_ne_hi
  apply Fin.ext
  rcases one with a | a | a | a | a <;> rcases two with b | b | b | b | b <;>
    simp_all [identifiers]

abbrev base : GeneralSourceState.State where
  slots := 5
  source := identifiers
  source_injective := identifiers_injective
  rowSource := identifiers
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev firstDescriptor : GeneralNominalState.Descriptor 5 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
abbrev lastDescriptor : GeneralNominalState.Descriptor 5 := ⟨0,⟨[.type],0⟩,[.type (2,2)],rfl⟩

noncomputable abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot.val = 0 then some firstDescriptor else
    if slot.val = 1 ∨ slot.val = 3 ∨ slot.val = 4 then some lastDescriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases recorded; rfl
    · split at recorded
      · cases recorded; rfl
      · cases recorded
  bodies_opaque := by intro _ _ _; rfl
  seed := after.current.context.state.seed
  allocated := after.current.context.state.allocated
  reserved := after.current.context.state.reserved
  ordinary := after.current.context.state.ordinary

noncomputable abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨snapshot,context.interpretation⟩
noncomputable def refreshed : GeneralNominalSupport.Tracked roles :=
  { after with current := regenerate after.current refreshedContext }

abbrev embed (slot : Fin 3) : Fin 5 := ⟨slot.val,by omega⟩

theorem source_embed (slot : Fin 3) : identifiers (embed slot) = slot.val := by
  have bound := slot.isLt
  simp [identifiers,show slot.val ≠ 3 by omega,show slot.val ≠ 4 by omega]

private theorem retained (slot : Fin 3) (d : GeneralNominalState.Descriptor 3)
    (recorded : source.nominals slot = some d) :
    snapshot.nominals (embed slot) = some (GeneralNominalRefinements.renameDescriptor embed d) := by
  have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
  rcases cases with zero | one | two
  · have same : slot = 0 := Fin.ext zero
    subst slot; cases recorded; rfl
  · have same : slot = 1 := Fin.ext one
    subst slot; cases recorded; rfl
  · have same : slot = 2 := Fin.ext two
    subst slot; cases recorded

noncomputable def refines : GeneralNominalRefinements.Refines after.current.context.state snapshot where
  base := ⟨embed,source_embed,source_embed,(by intro _ member; cases member),
    (by intro _ known; exact False.elim (known rfl)),(by intro _ member; cases member)⟩
  heads := by intro _ _ recorded; cases recorded
  nominals := retained
  ordinary := fun _ member => member
  known := by
    rintro identity ⟨slot,equal,head | nominal⟩
    · exact False.elim (head rfl)
    · obtain ⟨d,recorded⟩ := nominal
      exact ⟨embed slot,(source_embed slot).trans equal,Or.inr ⟨_,retained slot d recorded⟩⟩
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl


theorem lo_supported : lo ∈ GeneralNominalState.sources after.current.context.state := by
  exact (GeneralNominalSourceFormation.installation_reserves packet
    (GeneralNominalAllocation.origin root.identity capturedProposal.id 3 producerOnInput.id 0) (by
      simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
        capturedProposal,producerOnInput,consumerOnInput,Declaration.inputNames,Declaration.outputNames,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
        GeneralNominalDemandMerging.pointSite])).1

theorem hi_supported : hi ∈ GeneralNominalState.sources after.current.context.state := by
  exact (GeneralNominalSourceFormation.installation_reserves packet
    (GeneralNominalAllocation.origin root.identity capturedProposal.id 4 producerOnInput.id 0) (by
      simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
        capturedProposal,producerOnInput,consumerOnInput,Declaration.inputNames,Declaration.outputNames,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
        GeneralNominalDemandMerging.pointSite])).1

private theorem supported_slot (slot : Fin 5) : identifiers slot ∈ GeneralNominalState.sources after.current.context.state := by
  by_cases three : slot.val = 3
  · simpa [identifiers,three] using lo_supported
  by_cases four : slot.val = 4
  · simpa [identifiers,three,four] using hi_supported
  have bounded : slot.val < 3 := by omega
  rw [show identifiers slot = slot.val by simp [identifiers,three,four]]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_ofFn.mpr ⟨⟨slot.val,bounded⟩,rfl⟩)))

private theorem support : ∀ identity ∈ GeneralNominalState.sources snapshot,
    identity ∈ GeneralNominalState.sources after.current.context.state := by
  intro identity member
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((first | last) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp first
    exact equal ▸ supported_slot slot
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp last
    exact equal ▸ supported_slot slot
  · exact List.mem_append_left _ (List.mem_append_right _ reserved)
  · exact List.mem_append_right _ ordinary

noncomputable def certificate : GeneralNominalCycleSteps.Refresh after.current refreshedContext where
  refines := refines
  interpretation := rfl
  exact := by
    intro assignment valid
    have parent := valid.2.1 packet (by simp [after,GeneralNominalSharedSteps.install,GeneralNominalFeedbackSites.install])
    have original := ((GeneralNominalPacketSupport.packet_exact packet assignment).mp parent).1
    have chain := (GeneralNominalOutputGrowthModels.source_models 1 assignment).mp original
    refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,valid.1.2.2⟩
    · intro _ _ impossible; cases impossible
    · intro _ member; cases member
    · intro slot d recorded
      change Fin 5 at slot
      change GeneralNominalState.Descriptor 5 at d
      have possibilities : slot.val=0 ∨ slot.val=1 ∨ slot.val=2 ∨ slot.val=3 ∨ slot.val=4 := by omega
      rcases possibilities with zero | one | two | three | four
      · have eq : slot = 0 := Fin.ext zero
        subst slot; cases recorded
        apply (GeneralNominalState.denotes_singleton_exact base assignment 0 1 firstDescriptor rfl).mpr
        exact chain 0 (by omega)
      · have eq : slot = 1 := Fin.ext one
        subst slot; cases recorded
        apply (GeneralNominalState.denotes_singleton_exact base assignment 1 2 lastDescriptor rfl).mpr
        exact chain 1 (by omega)
      · have eq : slot = 2 := Fin.ext two
        subst slot; cases recorded
      · have eq : slot = 3 := Fin.ext three
        subst slot; cases recorded
        apply (GeneralNominalState.denotes_singleton_exact base assignment 3 2 lastDescriptor rfl).mpr
        exact endpoint_equation assignment valid lo (Or.inl rfl)
      · have eq : slot = 4 := Fin.ext four
        subst slot; cases recorded
        apply (GeneralNominalState.denotes_singleton_exact base assignment 4 2 lastDescriptor rfl).mpr
        exact endpoint_equation assignment valid hi (Or.inr rfl)
  support := support

theorem lo_known : GeneralNominalState.Known snapshot lo :=
  ⟨3,rfl,Or.inr ⟨lastDescriptor,rfl⟩⟩

theorem hi_known : GeneralNominalState.Known snapshot hi :=
  ⟨4,rfl,Or.inr ⟨lastDescriptor,rfl⟩⟩

theorem step : GeneralNominalSharedSteps.Step registry root after refreshed := by
  refine ⟨producer,children_generated.1,.administrative producer _ ?_⟩
  exact .refresh producer refreshedContext certificate lo lo_supported producer_still_unknown lo_known

theorem formed : GeneralNominalSharedSteps.SourceFormed registry root refreshed :=
  .update GeneralDictionarySharedCapturedInstallation.formed step

theorem models_exact (assignment : GeneralNominalCommonBridge.Assignment) :
    Models refreshed.current assignment ↔ Models after.current assignment :=
  GeneralNominalCycleSteps.refresh_models certificate assignment

theorem inhabited : Models refreshed.current model :=
  (models_exact model).mpr GeneralDictionarySharedCapturedInstallation.inhabited

theorem producer_ready : ¬ GeneralNominalState.RootPending snapshot producer.demand := by
  rintro ⟨index,unknown⟩
  rw [producer_inputs] at unknown
  exact unknown lo_known


theorem captured_unknown : ¬ GeneralNominalState.Known snapshot 2 := by
  rintro ⟨slot,equal,head | ⟨d,recorded⟩⟩
  · exact head rfl
  · have same : slot = (2 : Fin 5) := identifiers_injective equal
    subst slot; cases recorded

theorem consumer_pending : GeneralNominalState.RootPending snapshot GeneralDictionarySharedCapturedTargets.consumer.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rw [consumer_input]
  exact captured_unknown

theorem shared_prefix : B4Target.Steps (GeneralNominalSharedSteps.Step registry root)
    GeneralDictionarySharedCapturedInstallable.start refreshed :=
  .tail (.tail .refl GeneralDictionarySharedCapturedInstallation.step) step

end Yulang.GeneralDictionarySharedCapturedRefresh
