import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralNominalRefreshFork
import Yulang.GeneralNominalSettledIntervalDeclarations

/-! A point initial source whose certified refresh exposes an interval around
an actual cyclic argument. The recursive declaration is Paterson smaller. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalPointCycleSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralSourceState (equationAtoms)

abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.bareRole
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev child : Clause := ⟨0,0,[.app 0 [.var 0]],[]⟩
abbrev declaration : Declaration :=
  ⟨0,0,[.app 0 [.variant 0 (.var 0)]],[child],[],[]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,
      GeneralDeclarationExamples.bareRole,declaration,child]
  · simp [Declaration.Identified,Declaration.outputNames,declaration,child]
  · simp [Declaration.Produced,declaration,child]
  · simp [Declaration.OutputOnly,Declaration.outputNames,declaration,child]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,declaration,child,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,declaration,child]
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact ⟨rfl,rfl⟩
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    unfold ConservativeSmaller
    decide +kernel
  · intro clause member capture
    have same := List.mem_singleton.mp member; subst clause
    constructor
    · simp only [declaration,child,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size,List.map_cons,List.map_nil]
      omega
    · intro name
      simp only [declaration,child,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences,
        List.map_cons,List.map_nil]
      omega

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
theorem checked : Checked registry :=
  ⟨by decide +kernel,fun _ member => (List.mem_singleton.mp member) ▸ declaration_checked⟩

abbrev equations : List (PresenceNormalForm.Atom (Fin 7)) :=
  equationAtoms 0 (.var 1) ++ equationAtoms 2 (.variant 0 (.var 2)) ++
  equationAtoms 3 (.variant 0 (.var 5)) ++ equationAtoms 4 (.variant 0 (.var 6)) ++
  equationAtoms 5 .bottom ++ equationAtoms 6 .top

abbrev base : GeneralSourceState.State where
  slots := 7
  source := Fin.val
  source_injective := fun _ _ same => Fin.ext same
  rowSource := Fin.val
  ordinary := equations
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev views (slot : Fin 7) :
    GeneralNormalizedObservation.Head (fun _ : Fin 1 => .variant 0) 7 :=
  if slot = 2 then .structural 0 (fun _ => 2)
  else if slot = 3 then .structural 0 (fun _ => 5)
  else if slot = 4 then .structural 0 (fun _ => 6)
  else .deferred .unresolved

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .variant 0
  shapes_injective := fun _ _ _ => Subsingleton.elim _ _
  canonical := by intro _; trivial
  heads := views
  checked := by
    intro slot term seen
    unfold views at seen
    repeat first
      | split at seen
      | (rename_i same; subst slot; cases Option.some.inj seen
         exact .ordinary (by simp [base,equations,equationAtoms,GeneralNormalizedObservation.Shape.term])
           (by simp [base,equations,equationAtoms,GeneralNormalizedObservation.Shape.term]))
      | cases seen

abbrev descriptor (bounds : Fin 7 × Fin 7) : GeneralNominalState.Descriptor 7 :=
  ⟨0,⟨[.type],0⟩,[.type bounds],rfl⟩

abbrev state (wide : Bool) : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 1 then some (descriptor (2,2))
    else if slot = 0 ∧ wide = true then some (descriptor (3,4)) else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases Option.some.inj recorded; rfl
    · split at recorded
      · cases Option.some.inj recorded; rfl
      · cases recorded
  bodies_opaque := by
    intro slot d recorded
    split at recorded
    · rename_i same; subst slot; rfl
    · split at recorded
      · rename_i same; rcases same with ⟨rfl,_⟩; rfl
      · cases recorded
  seed := 6

abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun name => name == 0,by intro _ _; rfl⟩
abbrev context (wide : Bool) : GeneralNominalCandidates.Context := ⟨state wide,interpretation⟩
abbrev root : Occurrence roles :=
  ⟨7,⟨0,fun _ => (0,0),[],by intro _ impossible; cases impossible⟩⟩
abbrev start := GeneralNominalSupport.initial (context false) root
abbrev refreshed : GeneralNominalSupport.Tracked roles :=
  {start with current := regenerate start.current (context true)}

theorem source_member (wide : Bool) (slot : Fin 7) :
    slot.val ∈ GeneralNominalState.sources (state wide) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context false) root := by
  refine ⟨rfl,⟨rfl,by intro _ _ impossible; cases impossible⟩,?_,?_,?_,rfl⟩
  · exact ⟨fun _ => ⟨source_member false 0,source_member false 0⟩,by intro _ impossible; cases impossible⟩
  · intro _ _ _; exact subtype_refl _
  · intro identity present
    change identity ≤ 6
    simp only [GeneralNominalState.sources,state,List.mem_append,List.not_mem_nil,
      List.flatMap_nil,or_false] at present
    rcases present with first | last
    all_goals obtain ⟨slot,equal⟩ := List.mem_ofFn.mp ‹_›
    all_goals have bound := slot.isLt
    all_goals change slot.val < 7 at bound
    all_goals change slot.val = identity at equal
    all_goals omega

/-- Pointness is stated for every initial listed interval, nominal parameter,
and unnamed root argument, rather than only for the requested input. -/
theorem initial_point :
    (∀ bounds ∈ (state false).base.intervals, bounds.1 = bounds.2) ∧
    (∀ slot d, (state false).nominals slot = some d →
      ∀ bounds, GeneralNominalState.Parameter.type bounds ∈ d.arguments → bounds.1 = bounds.2) ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) := by
  refine ⟨(by intro _ impossible; cases impossible),?_,fun _ => rfl⟩
  intro slot d recorded bounds member
  by_cases one : slot = 1
  · subst slot
    cases Option.some.inj recorded
    have same := List.mem_singleton.mp member
    cases same
    rfl
  · simp [state,one] at recorded

theorem alias_zero (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 0).1 (m 1).1 :=
  ⟨valid.1.1 (.tyLe (.var 0) (.var 1)) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe (.var 1) (.var 0)) (by simp [base,equations,equationAtoms])⟩

theorem loop_two (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 2).1 (variant 0 (m 2).1) :=
  ⟨valid.1.1 (.tyLe (.var 2) (.variant 0 (.var 2))) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe (.variant 0 (.var 2)) (.var 2)) (by simp [base,equations,equationAtoms])⟩

theorem lower_three (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 3).1 (variant 0 (m 5).1) :=
  ⟨valid.1.1 (.tyLe (.var 3) (.variant 0 (.var 5))) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe (.variant 0 (.var 5)) (.var 3)) (by simp [base,equations,equationAtoms])⟩

theorem upper_four (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 4).1 (variant 0 (m 6).1) :=
  ⟨valid.1.1 (.tyLe (.var 4) (.variant 0 (.var 6))) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe (.variant 0 (.var 6)) (.var 4)) (by simp [base,equations,equationAtoms])⟩

theorem bottom_five (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 5).1 .bottom :=
  ⟨valid.1.1 (.tyLe (.var 5) .bottom) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe .bottom (.var 5)) (by simp [base,equations,equationAtoms])⟩

theorem top_six (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) : Equivalent (m 6).1 .top :=
  ⟨valid.1.1 (.tyLe (.var 6) .top) (by simp [base,equations,equationAtoms]),
   valid.1.1 (.tyLe .top (.var 6)) (by simp [base,equations,equationAtoms])⟩

theorem bottom_le (value : Ty) : Subtype .bottom value := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env observation accepted
  exact CommonNominalFullDemand.probeAt_bottom rank observation

theorem broad_bounds (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state wide) m) :
    Subtype (m 3).1 (m 2).1 ∧ Subtype (m 2).1 (m 4).1 := by
  constructor
  · exact subtype_trans (lower_three m valid).1
      (subtype_trans ((common_variant_iff 0 _ _).mpr (subtype_trans (bottom_five m valid).1 (bottom_le _)))
        (loop_two m valid).2)
  · exact subtype_trans (loop_two m valid).1
      (subtype_trans ((common_variant_iff 0 _ _).mpr
        (subtype_trans (GeneralNominalTopObservation.le_top _) (top_six m valid).2)) (upper_four m valid).2)

theorem refresh_models_forward (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state false) m) : GeneralNominalState.Models (state true) m := by
  refine ⟨valid.1,?_,valid.2.2⟩
  intro slot d recorded
  by_cases one : slot = 1
  · exact valid.2.1 slot d (by simpa [state,one] using recorded)
  by_cases zero : slot = 0
  · subst slot
    cases Option.some.inj recorded
    obtain ⟨values,fits,equal⟩ := valid.2.1 (1 : Fin 7) (descriptor (2,2)) rfl
    refine ⟨values,?_,subtype_trans (alias_zero m valid).1 equal.1,
      subtype_trans equal.2 (alias_zero m valid).2⟩
    change GeneralNominalState.FitsAll base m [.type (2,2)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases value with
      | inr => cases head
      | inl value =>
        exact .cons ⟨subtype_trans (broad_bounds m valid).1 head.1,
          subtype_trans head.2 (broad_bounds m valid).2⟩ .nil
  · simp [state,one,zero] at recorded

abbrev body : CommonNominalFullGuardedClosure.Body 1 0 := fun _ => .variant 0 (.inl 0)
abbrev mu := CommonNominalFullGuardedClosure.instantiate body Fin.elim0 0
abbrev box (value : Ty) : Ty := nominal 0 [.inl value]
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (match identity with
   | 0 | 1 => box mu | 2 => mu | 3 => variant 0 .bottom | 4 => variant 0 .top
   | 5 => .bottom | 6 => .top | _ => .base .int,Common.rowEmpty)

theorem mu_equation : Equivalent mu (variant 0 mu) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 1)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,variant] using equation

theorem source_models : GeneralNominalState.Models (state false) model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    simp only [base,equations,equationAtoms,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact subtype_refl _ | exact mu_equation.1 | exact mu_equation.2
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro slot d recorded
    by_cases one : slot = 1
    · subst slot
      cases Option.some.inj recorded
      exact ⟨[.inl mu],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,subtype_refl _,subtype_refl _⟩
    · simp [state,one] at recorded

noncomputable def refinement : GeneralNominalRefinements.Refines (state false) (state true) := by
  refine ⟨?_,?_,?_,(by intro _ h; exact h),?_,(by intro _ h; exact h),(by intro _ h; exact h),rfl,rfl⟩
  · refine ⟨id,(by intro _; rfl),(by intro _; rfl),?_,(by intro _ h; exact h),(by intro _ h; exact h)⟩
    intro atom member
    simp only [base,equations,equationAtoms,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [base,equations,equationAtoms,PresenceNormalForm.Atom.rename,Core.PresenceGeneration.TyTerm.rename]
  · intro _ _ impossible; cases impossible
  · intro slot d recorded
    by_cases one : slot = 1
    · subst slot
      cases Option.some.inj recorded
      rfl
    · simp [state,one] at recorded
  · rintro source ⟨slot,same,head | ⟨d,recorded⟩⟩
    · exact ⟨slot,same,Or.inl head⟩
    · by_cases one : slot = 1
      · subst slot
        cases Option.some.inj recorded
        exact ⟨1,same,Or.inr ⟨_,rfl⟩⟩
      · simp [state,one] at recorded

noncomputable def certificate : GeneralNominalFeedbackSteps.Refresh start.current (context true) where
  refines := refinement
  interpretation := rfl
  exact := fun m valid => refresh_models_forward m valid.1
  support := fun _ member => member

theorem zero_unknown : ¬ GeneralNominalState.Known (state false) 0 := by
  rintro ⟨slot,same,head | ⟨d,recorded⟩⟩
  · have zero : slot = 0 := Fin.ext same
    subst slot
    exact head rfl
  · have zero : slot = 0 := Fin.ext same
    subst slot
    cases recorded

theorem refresh_step : GeneralNominalSharedSteps.Step registry root start refreshed :=
  ⟨root,.root,.administrative root _ (.refresh root (context true) certificate 0
    (source_member false 0) zero_unknown ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩)⟩

theorem refreshed_formed : GeneralNominalSharedSteps.SourceFormed registry root refreshed :=
  .update (.initial (context false) initial_source) refresh_step

theorem refreshed_models : Models refreshed.current model :=
  (GeneralNominalCycleSteps.refresh_models certificate model).mpr
    ((GeneralNominalSaturationState.initial_models ..).mpr source_models)

end Yulang.GeneralNominalPointCycleSource
