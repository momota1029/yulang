import Yulang.GeneralDictionaryFeedbackExecutor
import Yulang.GeneralNominalNonpointInspectionExamples
import Yulang.GeneralNominalTopObservation

/-! Two actual certified refreshes of the same source state. The source denotes
list (list int) in both branches. One observation uses its exact parameter;
the other retains a wider parameter interval with upper endpoint top. -/
namespace Yulang.GeneralNominalRefreshFork

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralSourceState (equationAtoms equationAtoms_exact)
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)

abbrev base : GeneralSourceState.State where
  slots := 5
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.var 1) ++ equationAtoms 3 (.base .int) ++ equationAtoms 4 .top
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 3 then .scalar .int else .unresolved
  intervals := []
  heads_sound := by
    intro assignment models slot term recorded
    by_cases three : slot = 3
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 5)) = term := by
        simpa [GeneralSourceState.Head.equation] using recorded
      subst term
      exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
        ((PresenceNormalForm.all_append ..).mp models).1).2
    · simp [three,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 3 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases three : slot = 3
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 5)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head rfl
    · simp [three,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor (bounds : Fin 5 × Fin 5) : GeneralNominalState.Descriptor 5 :=
  ⟨0,⟨[.type],0⟩,[.type bounds],rfl⟩

abbrev state (choice : Option Bool) : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then choice.map (fun wide => descriptor (2,if wide then 4 else 2))
    else if slot = 1 then some (descriptor (2,2)) else if slot = 2 then some (descriptor (3,3)) else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases choice with
      | none => cases recorded
      | some wide => have same := Option.some.inj recorded; subst d; rfl
    · split at recorded
      · have same := Option.some.inj recorded; subst d; rfl
      · split at recorded
        · have same := Option.some.inj recorded; subst d; rfl
        · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases three : slot = 3
    · subst slot; simp at recorded
    · simp [view,three]

abbrev declaration : Declaration := ⟨90,0,[.app 0 [.app 0 [.app 2 []]]],[],[],[]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors]
  all_goals intro clause member; cases member

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
theorem registry_checked : Checked registry :=
  ⟨by simp,fun d member => (List.mem_singleton.mp member) ▸ declaration_checked⟩

abbrev context (choice : Option Bool) : Context := ⟨state choice,GeneralNominalExamples.interpretation⟩
abbrev root := GeneralNominalExamples.displayRoot
abbrev before := initial (context none) root
abbrev after (wide : Bool) := regenerate before (context (some wide))

theorem alias_zero (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state choice) m) : Equivalent (m 0).1 (m 1).1 := by
  exact ⟨valid.1.1 (.tyLe (.var 0) (.var 1)) (by simp [base,equationAtoms]),
    valid.1.1 (.tyLe (.var 1) (.var 0)) (by simp [base,equationAtoms])⟩

theorem scalar_three (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state choice) m) : Equivalent (m 3).1 (.base .int) :=
  valid.1.2.1 3 (.base .int) rfl

theorem top_four (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state choice) m) : Equivalent (m 4).1 .top := by
  exact ⟨valid.1.1 (.tyLe (.var 4) .top) (by simp [base,equationAtoms]),
    valid.1.1 (.tyLe .top (.var 4)) (by simp [base,equationAtoms])⟩

theorem refresh_models_forward (wide : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state none) m) : GeneralNominalState.Models (state (some wide)) m := by
  refine ⟨valid.1,?_,valid.2.2⟩
  intro slot d recorded
  by_cases zero : slot = 0
  · subst slot
    have same := Option.some.inj recorded
    subst d
    obtain ⟨values,fits,equal⟩ := valid.2.1 (1 : Fin 5) (descriptor (2,2)) rfl
    refine ⟨values,?_,subtype_trans (alias_zero m valid).1 equal.1,
      subtype_trans equal.2 (alias_zero m valid).2⟩
    change GeneralNominalState.FitsAll base m [.type (2,2)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases wide with
      | false => exact .cons head .nil
      | true =>
        cases value with
        | inr => cases head
        | inl value => exact .cons ⟨head.1,subtype_trans
            (GeneralNominalTopObservation.le_top value) (top_four m valid).2⟩ .nil
  · exact valid.2.1 slot d (by simpa [state,zero] using recorded)

noncomputable def refinement (wide : Bool) :
    GeneralNominalRefinements.Refines (state none) (state (some wide)) := by
  refine ⟨?_,?_,?_,(by intro _ h; exact h),?_,(by intro _ h; exact h),(by intro _ h; exact h),rfl,rfl⟩
  · refine ⟨id,(by intro _; rfl),(by intro _; rfl),?_,(by intro _ h; exact h),(by intro _ h; exact h)⟩
    intro atom member
    simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;>
      simp [base,equationAtoms,PresenceNormalForm.Atom.rename,Core.PresenceGeneration.TyTerm.rename]
  · intro slot term recorded
    by_cases three : slot = 3
    · subst slot
      have same : term = .base .int := Option.some.inj recorded.symm
      subst term
      exact .head rfl
    · simp [state,base,three,GeneralSourceState.Head.equation] at recorded
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; cases recorded
    · have same : GeneralNominalRefinements.renameDescriptor id d = d := by
        cases d; simp only [GeneralNominalRefinements.renameDescriptor]
        congr 1
        have rename : GeneralNominalRefinements.renameParameter (id : Fin 5 → Fin 5) = id := by
          funext parameter; cases parameter <;> rfl
        rw [rename]; exact List.map_id _
      change (state (some wide)).nominals slot = some (GeneralNominalRefinements.renameDescriptor id d)
      rw [same]
      simpa [state,zero] using recorded
  · rintro source ⟨slot,same,head | nominal⟩
    · exact ⟨slot,same,Or.inl head⟩
    · obtain ⟨d,recorded⟩ := nominal
      by_cases zero : slot = 0
      · subst slot; cases recorded
      · exact ⟨slot,same,Or.inr ⟨d,by simpa [state,zero] using recorded⟩⟩

noncomputable def certificate (wide : Bool) : GeneralNominalFeedbackSteps.Refresh before (context (some wide)) where
  refines := refinement wide
  interpretation := rfl
  exact := fun m valid => refresh_models_forward wide m valid.1
  support := fun _ member => member

theorem initial_pending : GeneralNominalState.RootPending (state none) root.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rintro ⟨slot,same,head | ⟨d,recorded⟩⟩
  · have zero : slot = 0 := Fin.ext same
    subst slot; exact head rfl
  · have zero : slot = 0 := Fin.ext same
    subst slot; cases recorded

theorem zero_known (wide : Bool) : GeneralNominalState.Known (state (some wide)) 0 :=
  ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩

theorem refresh_step (wide : Bool) : GeneralNominalFeedbackSteps.Step registry root before (after wide) :=
  ⟨root,.root,.refresh root (context (some wide)) (certificate wide) 0
    (by simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]; exact Or.inl (Or.inl (Or.inl ⟨⟨0,by decide +kernel⟩,rfl⟩)))
    (fun known => initial_pending.choose_spec known) (zero_known wide)⟩

theorem same_models (wide : Bool) (m : GeneralNominalCommonBridge.Assignment) :
    Models (after wide) m ↔ Models before m := GeneralNominalCycleSteps.refresh_models (certificate wide) m

abbrev list (value : Ty) : Ty := nominal 0 [.inl value]
abbrev model : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 ∨ source = 1 then list (list (.base .int))
    else if source = 2 then list (.base .int) else if source = 3 then .base .int else .top,Common.rowEmpty)

theorem initial_models : Models before model := by
  apply (GeneralNominalSaturationState.initial_models ..).mpr
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> exact subtype_refl _
  · intro slot term recorded
    by_cases three : slot = 3
    · subst slot
      have same : term = .base .int := Option.some.inj recorded.symm
      subst term; exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [context,state,base,three,GeneralSourceState.Head.equation] at recorded
  · intro pair member; cases member
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; cases recorded
    by_cases one : slot = 1
    · subst slot
      have same : descriptor (2,2) = d := Option.some.inj recorded
      subst d
      exact ⟨[.inl (list (.base .int))],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
        subtype_refl _,subtype_refl _⟩
    by_cases two : slot = 2
    · subst slot
      have same : descriptor (3,3) = d := Option.some.inj recorded
      subst d
      exact ⟨[.inl (.base .int)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
        subtype_refl _,subtype_refl _⟩
    · simp [context,state,zero,one,two] at recorded

theorem after_models (wide : Bool) : Models (after wide) model := (same_models wide model).mpr initial_models

theorem source_bound (choice : Option Bool) (source : Nat)
    (member : source ∈ GeneralNominalState.sources (state choice)) : source < 5 := by
  simp only [GeneralNominalState.sources,state,base,List.mem_append,List.mem_ofFn,List.not_mem_nil,
    List.flatMap_nil,or_false] at member
  rcases member with ⟨slot,rfl⟩ | ⟨slot,rfl⟩ <;> exact slot.isLt

theorem linked (choice : Option Bool) : GeneralNominalState.Linked (state choice) root.demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources,state,base,List.ofFn_succ]
  · intro output member; cases member

theorem metadata (choice : Option Bool) : Metadata registry (context choice) := by
  refine ⟨rfl,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive; exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context none) root := by
  refine ⟨rfl,metadata none,linked none,(by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  intro source member
  have bound := source_bound none source member
  change source ≤ 4
  omega

theorem initial_reachable : B4TargetV5.Reachable
    (GeneralDictionaryReachableBoundary.boundary roles) registry root before :=
  B4TargetV5.reachable_initial _ ⟨context none,initial_source,rfl⟩

theorem after_reachable (wide : Bool) : B4TargetV5.Reachable
    (GeneralDictionaryReachableBoundary.boundary roles) registry root (after wide) :=
  B4TargetV5.reachable_step _ initial_reachable (refresh_step wide)

theorem known_below_four (wide : Bool) (source : Nat) (bound : source < 4) :
    GeneralNominalState.Known (state (some wide)) source := by
  have cases : source = 0 ∨ source = 1 ∨ source = 2 ∨ source = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact zero_known wide
  · exact ⟨1,rfl,Or.inr ⟨_,rfl⟩⟩
  · exact ⟨2,rfl,Or.inr ⟨_,rfl⟩⟩
  · exact ⟨3,rfl,Or.inl (by intro impossible; cases impossible)⟩

theorem no_refresh (wide : Bool) (next : GeneralNominalCandidates.Context)
    (certified : GeneralNominalFeedbackSteps.Refresh (after wide) next)
    (source : Nat) (member : source ∈ GeneralNominalState.sources (state (some wide)))
    (unknown : ¬ GeneralNominalState.Known (state (some wide)) source) :
    ¬ GeneralNominalState.Known next.state source := by
  have bound := source_bound _ source member
  have four : source = 4 := by
    by_cases different : source = 4
    · exact different
    · exact False.elim (unknown (known_below_four wide source (by omega)))
  subst source
  exact GeneralNominalTopObservation.not_known next.state model 4
    (certified.exact model (after_models wide)) rfl

end Yulang.GeneralNominalRefreshFork
