import Yulang.GeneralNominalOutputGrowthPackets

/-! A real model-preserving feedback refresh after the first output-growth
installation. The new input head is entailed by the journal, the fresh output
identity is already reserved, and neither root nor candidate K2 rejects the
newly ready child. This is a finite two-update certificate. -/
namespace Yulang.GeneralNominalOutputGrowthRefresh

open GeneralNominalOutputGrowth GeneralNominalOutputGrowthModels GeneralNominalOutputGrowthPackets
open GeneralNominalSaturationState GeneralSourceDictionaries CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)

abbrev identifiers (slot : Fin 3) : Nat := if slot.val = 2 then output 0 else slot.val

abbrev refreshedBase : GeneralSourceState.State where
  slots := 3
  source := identifiers
  source_injective := by
    intro first last equal
    have fresh := output_fresh 0
    have one := first.isLt
    have two := last.isLt
    apply Fin.ext
    dsimp only [identifiers] at equal
    split at equal <;> split at equal <;> omega
  rowSource := identifiers
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev refreshedView : GeneralNormalizedObservation.Snapshot refreshedBase where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev firstDescriptor : GeneralNominalState.Descriptor 3 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
abbrev lastDescriptor : GeneralNominalState.Descriptor 3 := ⟨0,⟨[.type],0⟩,[.type (2,2)],rfl⟩

abbrev refreshedState : GeneralNominalState.State where
  base := refreshedBase
  view := refreshedView
  constructors := constructors
  nominals := fun slot => if slot.val = 0 then some firstDescriptor else if slot.val = 1 then some lastDescriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · split at recorded
      · have same := Option.some.inj recorded; subst d; rfl
      · cases recorded
  bodies_opaque := by intro _ _ _; rfl
  seed := 1
  allocated := (packet 0).privateContext.state.allocated
  reserved := (packet 0).privateContext.state.reserved
  ordinary := (packet 0).privateContext.state.ordinary

abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨refreshedState,(context 0).interpretation⟩
noncomputable def refreshed := regenerate (installed 0) refreshedContext

abbrev embed (slot : Fin 2) : Fin 3 := ⟨slot.val,by omega⟩

private theorem source_embed (slot : Fin 2) : identifiers (embed slot) = slot.val := by
  have small := slot.isLt
  simp [identifiers,show slot.val ≠ 2 by omega]

private theorem retained (slot : Fin 2) (d : GeneralNominalState.Descriptor 2)
    (recorded : (source 0).nominals slot = some d) :
    refreshedState.nominals (embed slot) = some (GeneralNominalRefinements.renameDescriptor embed d) := by
  change (if bound : slot.val ≤ 0 then some (descriptor 0 slot bound) else none) = some d at recorded
  split at recorded
  · rename_i bound
    have zero : slot = 0 := Fin.ext (by omega)
    subst slot
    have same := Option.some.inj recorded; subst d
    rfl
  · cases recorded

noncomputable def refines : GeneralNominalRefinements.Refines (installed 0).context.state refreshedState where
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

private theorem output_supported : output 0 ∈ GeneralNominalState.sources (installed 0).context.state := by
  exact (GeneralNominalSourceFormation.installation_reserves (packet 0)
    (GeneralNominalAllocation.origin (root 0).identity 2 2 1 0) (by
      simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
        GeneralDeclarations.Declaration.inputNames,GeneralDeclarations.Declaration.outputNames,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
        GeneralNominalDemandMerging.pointSite])).1

private theorem support : ∀ identity ∈ GeneralNominalState.sources refreshedState,
    identity ∈ GeneralNominalState.sources (installed 0).context.state := by
  intro identity member
  simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
  rcases member with ((first | last) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp first
    change identifiers slot = identity at equal
    subst identity
    by_cases two : slot.val = 2
    · simpa only [identifiers,ite_eq_left two,GeneralNominalState.sources,List.mem_append] using output_supported
    · have bounded : slot.val < 2 := by have small := slot.isLt; omega
      rw [show identifiers slot = slot.val by simp [identifiers,two]]
      exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,bounded⟩,rfl⟩)))
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp last
    change identifiers slot = identity at equal
    subst identity
    by_cases two : slot.val = 2
    · simpa only [identifiers,ite_eq_left two,GeneralNominalState.sources,List.mem_append] using output_supported
    · have bounded : slot.val < 2 := by have small := slot.isLt; omega
      rw [show identifiers slot = slot.val by simp [identifiers,two]]
      exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,bounded⟩,rfl⟩)))
  · exact Or.inl (Or.inr reserved)
  · exact Or.inr ordinary

noncomputable def refresh_certificate : GeneralNominalFeedbackSteps.Refresh (installed 0) refreshedContext where
  refines := refines
  interpretation := rfl
  exact := by
    intro model valid
    refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,valid.1.2.2⟩
    · intro _ _ impossible; cases impossible
    · intro _ member; cases member
    · intro slot d recorded
      change (if slot.val = 0 then some firstDescriptor else if slot.val = 1 then some lastDescriptor else none) = some d at recorded
      split at recorded
      · rename_i zero
        have equal : slot = 0 := Fin.ext zero; subst slot
        have same := Option.some.inj recorded; subst d
        apply (GeneralNominalState.denotes_singleton_exact refreshedBase model 0 1 firstDescriptor rfl).mpr
        exact ((snapshot_models 0 model).mp
          ((GeneralNominalFeedbackSites.install_models (snapshot 0) (packet 0) _ rfl model).mp valid).1) 0 (Nat.le_refl _)
      · split at recorded
        · rename_i _ one
          have equal : slot = 1 := Fin.ext one; subst slot
          have same := Option.some.inj recorded; subst d
          apply (GeneralNominalState.denotes_singleton_exact refreshedBase model 1 2 lastDescriptor rfl).mpr
          exact packet_output_equation 0 model (valid.2.1 (packet 0) (by simp [installed,GeneralNominalFeedbackSites.install]))
        · cases recorded
  support := support

theorem child_known : GeneralNominalState.Known refreshedState 1 :=
  ⟨1,rfl,Or.inr ⟨lastDescriptor,rfl⟩⟩

theorem refresh_step : GeneralNominalFeedbackSteps.Step registry (root 0) (installed 0) refreshed := by
  refine ⟨child 0,GeneralNominalFeedbackSteps.installed_children (snapshot 0) (packet 0) (child 0)
    (by rw [children_exact]; simp),?_⟩
  apply GeneralNominalFeedbackSteps.At.refresh (child 0) refreshedContext refresh_certificate 1
  · exact GeneralNominalRefinements.sources
      (GeneralNominalRefinements.installed registry (context 0) (root 0) declaration (bounds 0)) 1
      (source_member 0 1)
  · exact (child_pending 0).choose_spec
  · exact child_known

theorem refresh_models (model : GeneralNominalCommonBridge.Assignment) :
    Models refreshed model ↔ Models (installed 0) model :=
  GeneralNominalCycleSteps.refresh_models refresh_certificate model

theorem refreshed_formed : GeneralNominalFeedbackSteps.SourceFormed registry (root 0) refreshed :=
  .update (installed_formed 0) refresh_step

theorem child_ready : ¬ GeneralNominalState.RootPending refreshedState (child 0).demand := by
  rintro ⟨index,unknown⟩
  exact unknown child_known

theorem refreshed_acyclic (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle refreshed identity :=
  feedback_acyclic refreshed (finiteModel 1) ((refresh_models _).mpr (installed_models 0))
    (fun i => 2-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem raw_acyclic (slot : Fin refreshedState.base.slots) :
    ¬ GeneralNominalCycleK2.Cycle refreshedState slot := by
  have valid := ((refresh_models (finiteModel 1)).mpr (installed_models 0)).1
  have decreasing : ∀ first last, GeneralNominalCycleK2.Edge refreshedState first last →
      2-identifiers last < 2-identifiers first := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_,_⟩ | ⟨d,_,index,observed⟩
    · exact Fin.elim0 kind
    · obtain ⟨actual,seen,same⟩ := observed (finiteModel 1) valid
      exact observation_decreases (finiteModel 1) (fun i => 2-i) (fun _ => rfl)
        (identifiers first) (identifiers last) d.declaration.name index actual seen same
  have paths : ∀ first last, GeneralNominalCycleK2.Path refreshedState first last →
      2-identifiers last ≤ 2-identifiers first := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have one := decreasing _ _ edge
  have two := paths _ _ path
  omega

theorem child_not_rootK2 : ¬ GeneralNominalFeedbackK2.RootK2 refreshed (child 0) := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact refreshed_acyclic _ cycle

theorem child_not_candidateK2 : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed (child 0) := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact refreshed_acyclic _ cycle

theorem two_steps_ready :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalFeedbackSteps.SourceFormed registry (root 0) refreshed ∧
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry (root 0)) (snapshot 0) refreshed ∧
    Models refreshed (finiteModel 1) ∧
    ¬ GeneralNominalState.RootPending refreshedState (child 0).demand ∧
    ¬ GeneralNominalFeedbackK2.RootK2 refreshed (child 0) ∧
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed (child 0) :=
  ⟨checked,refreshed_formed,.tail (.tail .refl (install_step 0)) refresh_step,
    (refresh_models _).mpr (installed_models 0),child_ready,child_not_rootK2,child_not_candidateK2⟩

theorem different_inputs_not_merged : ¬ GeneralNominalFeedbackSites.SameInputs refreshed
    (GeneralNominalDemandMerging.pointSite (root 0))
    (GeneralNominalFeedbackSites.childSite (packet 0) (child 0)) := by
  intro same
  let first := GeneralNominalDemandMerging.pointSite (root 0)
  let last := GeneralNominalFeedbackSites.childSite (packet 0) (child 0)
  have valid := (refresh_models (finiteModel 1)).mpr (installed_models 0)
  have left := GeneralNominalFeedbackSites.recover_sound refreshed first (finiteModel 1) valid
    (point_holds (root 0) (finiteModel 1))
  have right := GeneralNominalFeedbackSites.recover_sound refreshed last (finiteModel 1) valid
    (GeneralNominalFeedbackSites.child_sound (packet 0) (child 0) (finiteModel 1) (finite_packet_models 0))
  have relation := same.2
  change GeneralNominalDemandMerging.All₂ _
    [GeneralNominalFeedbackSites.recoverOrigin refreshed first ⟨0,by decide +kernel⟩]
    [GeneralNominalFeedbackSites.recoverOrigin refreshed last ⟨0,by decide +kernel⟩] at relation
  cases relation with
  | cons related _ =>
    obtain ⟨a,b,one,two,equal⟩ := related
    have firstFits := left ⟨0,by decide +kernel⟩ a (by
      change some (GeneralNominalFeedbackSites.recoverOrigin refreshed first _) = some (some a)
      exact congrArg some one)
    have lastFits := right ⟨0,by decide +kernel⟩ b (by
      change some (GeneralNominalFeedbackSites.recoverOrigin refreshed last _) = some (some b)
      exact congrArg some two)
    obtain ⟨x,hx⟩ := firstFits.1
    obtain ⟨y,hy⟩ := lastFits.1
    have xfit := firstFits.2 x hx
    have yfit := lastFits.2 y hy
    have sameValue := (equal (finiteModel 1) valid).2.2 x y hx hy
    have impossible : Equivalent (tower 2) (tower 1) :=
      ⟨subtype_trans xfit.1 (subtype_trans sameValue.1 yfit.2),
        subtype_trans yfit.1 (subtype_trans sameValue.2 xfit.2)⟩
    have contradiction := (tower_equivalent 2 1).mp impossible
    cases contradiction

end Yulang.GeneralNominalOutputGrowthRefresh
