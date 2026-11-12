import Yulang.GeneralNominalReobservationExamples
import Yulang.GeneralDictionaryTerminalRefresh

/-! The exact refresh fork with one additional unconstrained named output.
The wide view is blocked; precise inspection can select a terminal declaration
whose associated int equation is not entailed by the unchanged source models. -/
namespace Yulang.GeneralNominalCanonicalOutputFork

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRefreshFork (base view descriptor)
open GeneralSourceState (equationAtoms)
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors outputRole)

abbrev state (choice : Option Bool) : GeneralNominalState.State :=
  { GeneralNominalRefreshFork.state choice with seed := 5, reserved := [5] }
abbrev context (choice : Option Bool) : Context := ⟨state choice,GeneralNominalExamples.interpretation⟩
abbrev equation : Equation := ⟨91,1,.app 2 []⟩
abbrev declaration : Declaration := ⟨90,2,[.app 0 [.app 0 [.app 2 []]]],[],[equation],[]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro entry member
      have same := List.mem_singleton.mp member
      subst entry
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name
        exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,outputRole,one] at present
    · intro clause member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors]
  all_goals intro clause member; cases member

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
theorem registry_checked : Checked registry :=
  ⟨by simp,fun d member => (List.mem_singleton.mp member) ▸ declaration_checked⟩

abbrev root : Occurrence roles := ⟨100,⟨2,fun _ => (0,0),[⟨1,5⟩],by
  intro output member
  have same := List.mem_singleton.mp member
  subst output
  exact ⟨none,rfl⟩⟩⟩
abbrev before := initial (context none) root
abbrev after (wide : Bool) := initial (context (some wide)) root

theorem state_models (choice : Option Bool) (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (state choice) m ↔
      GeneralNominalState.Models (GeneralNominalRefreshFork.state choice) m := Iff.rfl

noncomputable def refinement (wide : Bool) :
    GeneralNominalRefinements.Refines (state none) (state (some wide)) :=
  ⟨(GeneralNominalRefreshFork.refinement wide).base,(GeneralNominalRefreshFork.refinement wide).heads,
    (GeneralNominalRefreshFork.refinement wide).nominals,(GeneralNominalRefreshFork.refinement wide).ordinary,
    (GeneralNominalRefreshFork.refinement wide).known,(by intro _ member; exact member),
    (by intro _ member; exact member),rfl,rfl⟩

noncomputable def certificate (wide : Bool) : GeneralNominalFeedbackSteps.Refresh before (context (some wide)) where
  refines := refinement wide
  interpretation := rfl
  exact := fun m valid => GeneralNominalRefreshFork.refresh_models_forward wide m valid.1
  support := fun _ member => member

theorem zero_known (wide : Bool) : GeneralNominalState.Known (state (some wide)) 0 :=
  GeneralNominalRefreshFork.zero_known wide

theorem refresh_step (wide : Bool) : GeneralNominalFeedbackSteps.Step registry root before (after wide) := by
  refine ⟨root,.root,.refresh root (context (some wide)) (certificate wide) 0 ?_ ?_ (zero_known wide)⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨(0 : Fin 5),rfl⟩)))
  · exact fun known => GeneralNominalRefreshFork.initial_pending.choose_spec known

theorem same_models (wide : Bool) (m : GeneralNominalCommonBridge.Assignment) :
    Models (after wide) m ↔ Models before m := GeneralNominalCycleSteps.refresh_models (certificate wide) m

abbrev model (scalar : Inference.Base) : GeneralNominalCommonBridge.Assignment := fun source =>
  if source = 5 then (.base scalar,Common.rowEmpty) else GeneralNominalRefreshFork.model source

theorem initial_models (scalar : Inference.Base) : Models before (model scalar) := by
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
    · simp [context,state,GeneralNominalRefreshFork.state,base,three,GeneralSourceState.Head.equation] at recorded
  · intro pair member; cases member
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; cases recorded
    by_cases one : slot = 1
    · subst slot
      have same : descriptor (2,2) = d := Option.some.inj recorded
      subst d
      exact ⟨[.inl (GeneralNominalRefreshFork.list (.base .int))],
        .cons ⟨subtype_refl _,subtype_refl _⟩ .nil,subtype_refl _,subtype_refl _⟩
    by_cases two : slot = 2
    · subst slot
      have same : descriptor (3,3) = d := Option.some.inj recorded
      subst d
      exact ⟨[.inl (.base .int)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
        subtype_refl _,subtype_refl _⟩
    · simp [context,state,GeneralNominalRefreshFork.state,zero,one,two] at recorded

theorem after_models (wide : Bool) (scalar : Inference.Base) : Models (after wide) (model scalar) :=
  (same_models wide _).mpr (initial_models scalar)

theorem source_bound (choice : Option Bool) (source : Nat)
    (member : source ∈ GeneralNominalState.sources (state choice)) : source ≤ 5 := by
  simp only [GeneralNominalState.sources,state,GeneralNominalRefreshFork.state,base,List.mem_append,
    List.mem_ofFn,List.mem_cons,List.not_mem_nil,List.flatMap_nil,or_false] at member
  rcases member with (⟨slot,rfl⟩ | ⟨slot,rfl⟩) | rfl <;> omega

theorem linked (choice : Option Bool) : GeneralNominalState.Linked (state choice) root.demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources,state,GeneralNominalRefreshFork.state,base,List.ofFn_succ]
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    simp [GeneralNominalState.sources,state]

theorem metadata (choice : Option Bool) : Metadata registry (context choice) :=
  GeneralNominalRefreshFork.metadata choice

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context none) root :=
  ⟨rfl,metadata none,linked none,(by intro _ _ _; exact subtype_refl _),source_bound none,rfl⟩

theorem initial_reachable : B4TargetV5.Reachable
    (GeneralDictionaryReachableBoundary.boundary roles) registry root before :=
  B4TargetV5.reachable_initial _ ⟨context none,initial_source,rfl⟩

theorem after_reachable (wide : Bool) : B4TargetV5.Reachable
    (GeneralDictionaryReachableBoundary.boundary roles) registry root (after wide) :=
  B4TargetV5.reachable_step _ initial_reachable (refresh_step wide)

theorem no_refresh (wide : Bool) (next : GeneralNominalCandidates.Context)
    (certified : GeneralNominalFeedbackSteps.Refresh (after wide) next)
    (source : Nat) (member : source ∈ GeneralNominalState.sources (state (some wide)))
    (unknown : ¬ GeneralNominalState.Known (state (some wide)) source) :
    ¬ GeneralNominalState.Known next.state source := by
  have bound := source_bound _ source member
  have large : 4 ≤ source := by
    by_cases small : source < 4
    · exact False.elim (unknown (GeneralNominalRefreshFork.known_below_four wide source small))
    · omega
  have cases : source = 4 ∨ source = 5 := by omega
  rcases cases with rfl | rfl
  · exact GeneralNominalTopObservation.not_known next.state (model .int) 4
      (certified.exact _ (after_models wide .int)) rfl
  · exact GeneralDictionaryTerminalRefresh.no_known_distinct next.state (model .int) (model .str) 5 rfl rfl
      (certified.exact _ (after_models wide .int)) (certified.exact _ (after_models wide .str))

noncomputable def revision : GeneralNominalReobservationSteps.Revision (after true) where
  entries := (state (some false)).nominals
  catalogue := (state (some false)).catalogue
  opaqueHeads := (state (some false)).bodies_opaque
  domain := GeneralNominalReobservationExamples.revision.domain

theorem revision_result : revision.result = after false := rfl

theorem revision_certified : GeneralNominalReobservationSteps.Certified revision where
  raw := GeneralNominalReobservationExamples.revision_certified.raw
  exact := fun m => (same_models false m).trans (same_models true m).symm

theorem revision_improves : GeneralNominalReobservationSteps.Improves revision :=
  GeneralNominalReobservationExamples.revision_improves

theorem repair_step : GeneralNominalReobservationSteps.Step registry root (after true) (after false) :=
  ⟨root,.root,.reobserve root revision revision_certified revision_improves⟩

end Yulang.GeneralNominalCanonicalOutputFork
