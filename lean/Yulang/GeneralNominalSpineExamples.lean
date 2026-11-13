import Yulang.GeneralNominalSpineAccessibility
import Yulang.GeneralNominalPeelingSources

/-! A binary recursive role retains one decreasing input while materializing
a compound second input. The registry and point sources are concrete data. -/
namespace Yulang.GeneralNominalSpineExamples
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalSpineAccessibility
open GeneralNominalActualInspectionSteps (Step)

abbrev recursiveChild : Clause := ⟨170,4,[.var 0,.app 0 [.var 1]],[]⟩
abbrev recursiveDecl : Declaration :=
  ⟨170,4,[.app 0 [.var 0],.app 0 [.var 1]],[recursiveChild],[],[]⟩
abbrev terminalDecl : Declaration := ⟨171,4,[.app 2 [],.var 1],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[recursiveDecl,terminalDecl]⟩

theorem recursive_checked : DeclarationChecked constructors roles recursiveDecl := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,GeneralDeclarationExamples.binaryRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member; cases List.mem_singleton.mp member
    intro capture
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,
        Pattern.encode,Roles.argsSize,Roles.Term.size]
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,
        Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem terminal_checked : DeclarationChecked constructors roles terminalDecl := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.binaryRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  rcases List.mem_cons.mp member with rfl | member
  · exact recursive_checked
  · cases List.mem_singleton.mp member; exact terminal_checked

abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨170,⟨4,fun _ => (0,0),[],by intro _ impossible; cases impossible⟩⟩

theorem spine (context : GeneralNominalCandidates.Context)
    (constructorsEq : context.state.constructors = constructors)
    (interpretation : context.interpretation = GeneralNominalExamples.interpretation) :
    Spine roles registry context (fun role => role = 4) 0 := by
  constructor
  · intro role live; cases live; decide +kernel
  · intro declaration visible live nonempty
    rcases List.mem_cons.mp visible with rfl | visible
    · refine ⟨0,[.nominal 0 [.variables [1]]],?_,by decide +kernel,?_⟩
      · simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
          GeneralNominalInspection.translate,constructorsEq,interpretation,GeneralNominalExamples.interpretation]
      · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
    · cases List.mem_singleton.mp visible
      exact False.elim (nonempty rfl)

theorem not_unary_peeling (context : GeneralNominalCandidates.Context) :
    ¬ GeneralNominalPeelingAccessibility.Peeling roles registry context (fun role => role = 4) 0 := by
  intro old
  have impossible := old.unary 4 rfl
  change 2 = 1 at impossible
  contradiction

theorem initial_source (length : Nat) : GeneralNominalSourceFormation.InitialSource registry
    (GeneralNominalPeelingSources.context length) root := by
  have old := GeneralNominalPeelingSources.initial_source length
  refine ⟨rfl,old.metadata,?_,(by intro _ _ _; exact CommonNominalFullCarrier.subtype_refl _),old.below_seed,old.unallocated⟩
  constructor
  · intro index
    exact old.linked.1 ⟨0,by decide +kernel⟩
  · intro output impossible; cases impossible

theorem point_source (length : Nat) : GeneralNominalActualBudget.PointSource
    (GeneralNominalPeelingSources.context length) root :=
  ⟨(GeneralNominalPeelingSources.point_source length).intervals,
    (GeneralNominalPeelingSources.point_source length).nominalTypes,
    (GeneralNominalPeelingSources.point_source length).nominalRows,by intro index; rfl⟩

theorem depth_bound (length : Nat) : GeneralNominalInvocationAncestry.InstalledDepthBound registry
    (GeneralNominalPeelingSources.context length) root (length+1) :=
  installed_depth_bound (spine _ rfl rfl) (initial_source length) rfl (by rfl)
    (GeneralNominalPeelingSources.ground length)

theorem accessible (length : Nat) : Acc (fun next current => Step registry root current next)
    (GeneralNominalSupport.initial (GeneralNominalPeelingSources.context length) root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked (initial_source length) (depth_bound length)

theorem initial_inhabited (length : Nat) : ∃ model,
    GeneralNominalSaturationState.Models
      (GeneralNominalSupport.initial (GeneralNominalPeelingSources.context length) root).current model := by
  obtain ⟨model,valid⟩ := GeneralNominalPeelingSources.source_inhabited length
  exact ⟨model,(GeneralNominalSaturationState.initial_models _ _ _).mpr valid⟩

theorem concrete_compound_recursion :
    recursiveDecl.requirements = [recursiveChild] ∧ recursiveChild.role = recursiveDecl.role ∧
      recursiveChild.arguments = [.var 0,.app 0 [.var 1]] ∧
      Acc (fun next current => Step registry root current next)
        (GeneralNominalSupport.initial (GeneralNominalPeelingSources.context 1) root) :=
  ⟨rfl,rfl,rfl,accessible 1⟩

end Yulang.GeneralNominalSpineExamples
