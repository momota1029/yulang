import Yulang.GeneralNominalSpineExamples

/-! Binary recursive examples with a demanded materialized output, first from
an input capture and then from an output-only binder produced by the child. -/
namespace Yulang.GeneralNominalSpineOutputs
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSpineAccessibility
open GeneralDeclarationExamples (constructors)
open GeneralNominalActualInspectionSteps (Step)

abbrev roles : Roles.RoleDecls := fun _ =>
  ⟨2,fun name => if name = 0 then some none else none,by
    intro name rhs impossible
    split at impossible <;> cases impossible⟩

abbrev childOutput : Equation := ⟨181,0,.var 2⟩
abbrev child (bind : Bool) : Clause :=
  ⟨180,4,[.var 0,.app 0 [.var 1]],if bind then [childOutput] else []⟩
abbrev output (bind : Bool) : Equation := ⟨182,0,if bind then .var 2 else .app 0 [.var 1]⟩
abbrev declaration (bind : Bool) : Declaration :=
  ⟨180,4,[.app 0 [.var 0],.app 0 [.var 1]],[child bind],[output bind],
    if bind then [⟨2,180,181⟩] else []⟩
abbrev terminal : Declaration := ⟨183,4,[.app 2 [],.var 1],[],[⟨184,0,.var 1⟩],[]⟩
abbrev registry (bind : Bool) : Registry := ⟨constructors,roles,[declaration bind,terminal]⟩

private theorem signature (bind : Bool) : (declaration bind).Signature roles := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro equation member
    cases List.mem_singleton.mp member
    exact ⟨none,rfl⟩
  · intro name body defined
    by_cases zero : name = 0
    · subst name; exact Or.inl ⟨output bind,by simp,rfl⟩
    · simp [zero] at defined
  · intro clause member
    cases List.mem_singleton.mp member
    refine ⟨rfl,?_⟩
    cases bind with
    | false => intro equation impossible; cases impossible
    | true =>
      intro equation member
      cases List.mem_singleton.mp member
      exact ⟨none,rfl⟩

theorem declaration_checked (bind : Bool) : DeclarationChecked constructors roles (declaration bind) := by
  constructor
  · exact signature bind
  · cases bind <;> simp [Declaration.Identified,Declaration.outputNames]
  · cases bind <;> simp [Declaration.Produced]
  · cases bind <;> simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · cases bind <;> simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · cases bind <;> simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact GeneralNominalSpineExamples.recursive_checked.paterson GeneralNominalSpineExamples.recursiveChild (by simp)
  · intro clause member; cases List.mem_singleton.mp member
    exact GeneralNominalSpineExamples.recursive_checked.conservative GeneralNominalSpineExamples.recursiveChild (by simp)
  · intro clause member; cases List.mem_singleton.mp member
    exact GeneralNominalSpineExamples.recursive_checked.captureStable GeneralNominalSpineExamples.recursiveChild (by simp)

theorem terminal_checked : DeclarationChecked constructors roles terminal := by
  constructor
  · refine ⟨rfl,?_,?_,by intro clause impossible; cases impossible⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body defined
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨⟨184,0,.var 1⟩,by simp,rfl⟩
      · simp [zero] at defined
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem checked (bind : Bool) : Checked (registry bind) := by
  refine ⟨by simp,?_⟩
  intro decl member
  rcases List.mem_cons.mp member with rfl | member
  · exact declaration_checked bind
  · cases List.mem_singleton.mp member; exact terminal_checked

abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨180,⟨4,fun _ => (0,0),[⟨0,0⟩],by
    intro requested member
    cases List.mem_singleton.mp member
    exact ⟨none,rfl⟩⟩⟩

theorem spine (bind : Bool) (context : GeneralNominalCandidates.Context)
    (constructorsEq : context.state.constructors = constructors)
    (interpretation : context.interpretation = GeneralNominalExamples.interpretation) :
    Spine roles (registry bind) context (fun role => role = 4) 0 := by
  constructor
  · intro role live; change 0 < 2; omega
  · intro decl visible live nonempty
    rcases List.mem_cons.mp visible with rfl | visible
    · refine ⟨0,[.nominal 0 [.variables [1]]],?_,by decide +kernel,?_⟩
      · simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
          GeneralNominalInspection.translate,constructorsEq,interpretation,GeneralNominalExamples.interpretation]
      · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
    · cases List.mem_singleton.mp visible; exact False.elim (nonempty rfl)

theorem initial_source (bind : Bool) (length : Nat) : GeneralNominalSourceFormation.InitialSource
    (registry bind) (GeneralNominalPeelingSources.context length) root := by
  have old := GeneralNominalPeelingSources.initial_source length
  refine ⟨rfl,old.metadata,?_,(by intro _ _ _; exact CommonNominalFullCarrier.subtype_refl _),old.below_seed,old.unallocated⟩
  constructor
  · intro index; exact old.linked.1 ⟨0,by decide +kernel⟩
  · intro requested member
    cases List.mem_singleton.mp member
    exact (old.linked.1 ⟨0,by decide +kernel⟩).1

theorem point_source (length : Nat) : GeneralNominalActualBudget.PointSource
    (GeneralNominalPeelingSources.context length) root :=
  ⟨(GeneralNominalPeelingSources.point_source length).intervals,
    (GeneralNominalPeelingSources.point_source length).nominalTypes,
    (GeneralNominalPeelingSources.point_source length).nominalRows,by intro index; rfl⟩

theorem accessible (bind : Bool) (length : Nat) : Acc (fun next current => Step (registry bind) root current next)
    (GeneralNominalSupport.initial (GeneralNominalPeelingSources.context length) root) :=
  GeneralNominalSpineAccessibility.accessible (checked bind) (spine bind _ rfl rfl)
    (initial_source bind length) rfl (by rfl) (GeneralNominalPeelingSources.ground length)

theorem initial_inhabited (length : Nat) : ∃ model,
    GeneralNominalSaturationState.Models
      (GeneralNominalSupport.initial (GeneralNominalPeelingSources.context length) root).current model := by
  obtain ⟨model,valid⟩ := GeneralNominalPeelingSources.source_inhabited length
  exact ⟨model,(GeneralNominalSaturationState.initial_models _ _ _).mpr valid⟩

theorem without_binders : (declaration false).outputBinders = [] ∧
    (declaration false).associated ≠ [] := ⟨rfl,by simp⟩

theorem materialized_request (bind : Bool) :
    GeneralNominalMaterialization.rootRequests (declaration bind) root =
      [⟨(output bind).rhs,0,.actual⟩] := by
  simp [GeneralNominalMaterialization.rootRequests]

theorem binder_producer :
    (declaration true).outputBinders = [⟨2,180,181⟩] ∧
      (child true).outputs = [⟨181,0,.var 2⟩] ∧ (output true).rhs = .var 2 :=
  ⟨rfl,rfl,rfl⟩

end Yulang.GeneralNominalSpineOutputs
