import Yulang.GeneralDeclarationExamples

/-! The six declarations of the hidden-capture provenance stress test.
These use the general declaration check, including capture-stable descent.
No source state, applicability judgment, or transition is assumed here. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenanceDeclarations
open GeneralDeclarationPatterns GeneralDeclarations GeneralDeclarationDemands

abbrev bareRole (arity : Nat) : Roles.RoleDecl := ⟨arity,fun _ => none,by intros; contradiction⟩
abbrev outputRole (arity output : Nat) : Roles.RoleDecl :=
  ⟨arity,fun name => if name = output then some none else none,by
    intro name rhs impossible
    split at impossible <;> cases impossible⟩
abbrev roles : Roles.RoleDecls
  | 0 => bareRole 3
  | 1 | 2 => outputRole 3 0
  | 3 | 4 => outputRole 2 1
  | 5 => outputRole 1 1
  | _ => bareRole 0
abbrev constructors := GeneralDeclarationExamples.constructors

abbrev extractA : Clause := ⟨10,5,[.app 0 [.var 0]],[⟨100,1,.var 3⟩]⟩
abbrev childW : Clause := ⟨11,1,[.app 0 [.var 0],.app 0 [.var 1],.var 2],[⟨110,0,.var 3⟩]⟩
abbrev extractB : Clause := ⟨12,5,[.app 0 [.var 1]],[⟨120,1,.var 4⟩]⟩
abbrev childG : Clause := ⟨13,2,[.app 0 [.var 1],.app 0 [.var 0],.var 2],[⟨130,0,.var 4⟩]⟩
abbrev childP : Clause := ⟨14,0,[.app 0 [.var 0],.app 0 [.var 1],.var 2],[]⟩
abbrev p : Declaration :=
  ⟨0,0,[.app 0 [.app 0 [.var 0]],.app 0 [.app 0 [.var 1]],.var 2],
    [extractA,childW,extractB,childG,childP],[],[⟨3,10,100⟩,⟨4,12,120⟩]⟩
abbrev childC : Clause := ⟨20,3,[.var 1,.var 2],[⟨200,1,.var 3⟩]⟩
abbrev childD : Clause := ⟨30,4,[.var 1,.var 2],[⟨300,1,.var 3⟩]⟩
abbrev w : Declaration := ⟨1,1,[.app 0 [.var 0],.var 1,.var 2],
  [childC],[⟨201,0,.app 0 [.var 3]⟩],[⟨3,20,200⟩]⟩
abbrev g : Declaration := ⟨2,2,[.app 0 [.var 0],.var 1,.var 2],
  [childD],[⟨301,0,.app 0 [.var 3]⟩],[⟨3,30,300⟩]⟩
abbrev c : Declaration := ⟨3,3,[.app 0 [.var 0],.app 1 [.app 2 []]],[],[⟨401,1,.var 0⟩],[]⟩
abbrev d : Declaration := ⟨4,4,[.app 0 [.var 0],.app 1 [.app 2 []]],[],[⟨501,1,.var 0⟩],[]⟩
abbrev extract : Declaration := ⟨5,5,[.app 0 [.var 0]],[],[⟨601,1,.var 0⟩],[]⟩

private theorem p_stable (clause : Clause) (member : clause ∈ p.requirements) :
    StableSmaller p.head clause.arguments := by
  simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    intro capture
    constructor
    · simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
      omega

private theorem branch_stable :
    StableSmaller [.app 0 [.var 0],.var 1,.var 2] [.var 1,.var 2] := by
  intro capture
  constructor
  · simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,
      encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
    omega
  · intro name
    simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,
      encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
    omega

theorem p_checked : DeclarationChecked constructors roles p := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,bareRole,outputRole,
      p,extractA,childW,extractB,childG,childP]
  · simp [Declaration.Identified,Declaration.outputNames,p,extractA,childW,extractB,childG,childP]
  · simp [Declaration.Produced,p,extractA,childW,extractB,childG,childP]
  · simp [Declaration.OutputOnly,Declaration.outputNames,p,extractA,childW,extractB,childG,childP,
      variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,p,extractA,childW,extractB,childG,childP,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,
      p,extractA,childW,extractB,childG,childP]
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · exact p_stable

theorem w_checked : DeclarationChecked constructors roles w := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨⟨201,0,.app 0 [.var 3]⟩,by simp,rfl⟩
      · simp [roles,outputRole,zero] at present
    · intro clause member
      have same := List.mem_singleton.mp member; subst clause
      refine ⟨rfl,?_⟩
      intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames,w,childC]
  · simp [Declaration.Produced,w,childC]
  · simp [Declaration.OutputOnly,Declaration.outputNames,w,childC,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,w,childC,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,w,childC]
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause; exact ⟨rfl,rfl⟩
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    unfold ConservativeSmaller; decide +kernel
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact branch_stable

theorem g_checked : DeclarationChecked constructors roles g := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨⟨301,0,.app 0 [.var 3]⟩,by simp,rfl⟩
      · simp [roles,outputRole,zero] at present
    · intro clause member
      have same := List.mem_singleton.mp member; subst clause
      refine ⟨rfl,?_⟩
      intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames,g,childD]
  · simp [Declaration.Produced,g,childD]
  · simp [Declaration.OutputOnly,Declaration.outputNames,g,childD,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,g,childD,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,g,childD]
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause; exact ⟨rfl,rfl⟩
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    unfold ConservativeSmaller; decide +kernel
  · intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact branch_stable

theorem c_checked : DeclarationChecked constructors roles c := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name; exact Or.inl ⟨⟨401,1,.var 0⟩,by simp,rfl⟩
      · simp [roles,outputRole,one] at present
    · intro clause impossible; cases impossible
  · simp [Declaration.Identified,Declaration.outputNames,c]
  · simp [Declaration.Produced,c]
  · simp [Declaration.OutputOnly,Declaration.outputNames,c]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,c,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,c]
  all_goals intro clause impossible; cases impossible

theorem d_checked : DeclarationChecked constructors roles d := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name; exact Or.inl ⟨⟨501,1,.var 0⟩,by simp,rfl⟩
      · simp [roles,outputRole,one] at present
    · intro clause impossible; cases impossible
  · simp [Declaration.Identified,Declaration.outputNames,d]
  · simp [Declaration.Produced,d]
  · simp [Declaration.OutputOnly,Declaration.outputNames,d]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,d,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,d]
  all_goals intro clause impossible; cases impossible

theorem extract_checked : DeclarationChecked constructors roles extract := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name; exact Or.inl ⟨⟨601,1,.var 0⟩,by simp,rfl⟩
      · simp [roles,outputRole,one] at present
    · intro clause impossible; cases impossible
  · simp [Declaration.Identified,Declaration.outputNames,extract]
  · simp [Declaration.Produced,extract]
  · simp [Declaration.OutputOnly,Declaration.outputNames,extract]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,extract,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,extract]
  all_goals intro clause impossible; cases impossible

abbrev registry : Registry := ⟨constructors,roles,[p,w,g,c,d,extract]⟩

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p_checked
  · exact w_checked
  · exact g_checked
  · exact c_checked
  · exact d_checked
  · exact extract_checked

/-- The two pairs of associated requests share their output-only source
identities independently of the allocator. -/
theorem p_emitted_outputs (invocation : Nat) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    ((emitAll invocation p p_checked.signature capture allocate).map (fun emission => emission.demand.outputs)) =
      [[⟨1,capture.outputs 3⟩],[⟨0,capture.outputs 3⟩],
       [⟨1,capture.outputs 4⟩],[⟨0,capture.outputs 4⟩],[]] := by
  simp [emitAll,emit,childDemand,outputTarget,Declaration.outputNames,
    normalize,p,extractA,childW,extractB,childG,childP]

/-- Compound unnamed inputs retain allocated lower and upper endpoints;
only a bare variable directly reuses the captured interval. -/
theorem w_emitted_inputs (capture : Capture) (allocation : Allocation roles childW) :
    (childDemand p childW (p_checked.signature.2.2.2 childW (by simp)) capture allocation).arguments =
      (fun index => if index.val = 0 then allocation.arguments ⟨0,by decide +kernel⟩
        else if index.val = 1 then allocation.arguments ⟨1,by decide +kernel⟩ else capture.inputs 2) := by
  funext index
  have bound : index.val < 3 := index.isLt
  have cases : index = (0 : Fin 3) ∨ index = (1 : Fin 3) ∨ index = (2 : Fin 3) := by
    have : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 := by omega
    rcases this with equal | equal | equal
    · exact Or.inl (Fin.ext equal)
    · exact Or.inr (Or.inl (Fin.ext equal))
    · exact Or.inr (Or.inr (Fin.ext equal))
  rcases cases with rfl | rfl | rfl <;> simp [childDemand,inputInterval,normalize]

theorem w_child_inputs_outputs (capture : Capture) (allocation : Allocation roles childC) :
    (childDemand w childC (w_checked.signature.2.2.2 childC (by simp)) capture allocation).arguments =
      (fun index => if index.val = 0 then capture.inputs 1 else capture.inputs 2) ∧
    (childDemand w childC (w_checked.signature.2.2.2 childC (by simp)) capture allocation).outputs =
      [⟨1,capture.outputs 3⟩] := by
  constructor
  · funext index
    have bound : index.val < 2 := index.isLt
    have cases : index = (0 : Fin 2) ∨ index = (1 : Fin 2) := by
      have : index.val = 0 ∨ index.val = 1 := by omega
      rcases this with equal | equal
      · exact Or.inl (Fin.ext equal)
      · exact Or.inr (Fin.ext equal)
    rcases cases with rfl | rfl <;> simp [childDemand,inputInterval,normalize]
  · simp [childDemand,outputTarget,Declaration.outputNames,normalize,w,childC]

theorem g_child_inputs_outputs (capture : Capture) (allocation : Allocation roles childD) :
    (childDemand g childD (g_checked.signature.2.2.2 childD (by simp)) capture allocation).arguments =
      (fun index => if index.val = 0 then capture.inputs 1 else capture.inputs 2) ∧
    (childDemand g childD (g_checked.signature.2.2.2 childD (by simp)) capture allocation).outputs =
      [⟨1,capture.outputs 3⟩] := by
  constructor
  · funext index
    have bound : index.val < 2 := index.isLt
    have cases : index = (0 : Fin 2) ∨ index = (1 : Fin 2) := by
      have : index.val = 0 ∨ index.val = 1 := by omega
      rcases this with equal | equal
      · exact Or.inl (Fin.ext equal)
      · exact Or.inr (Fin.ext equal)
    rcases cases with rfl | rfl <;> simp [childDemand,inputInterval,normalize]
  · simp [childDemand,outputTarget,Declaration.outputNames,normalize,g,childD]

theorem no_output_binder_in_inputs (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (clause : Clause) (member : clause ∈ declaration.requirements) (name : Nat)
    (output : name ∈ declaration.outputNames) : name ∉ variablesArgs clause.arguments :=
  (checked.2 declaration visible).outputOnly.2 clause member name output

theorem counted_sizes : Roles.argsSize (counted p.head) = 7 ∧
    Roles.argsSize (counted childW.arguments) = 5 ∧
    Roles.argsSize (counted childG.arguments) = 5 ∧
    Roles.argsSize (counted childP.arguments) = 5 ∧
    Roles.argsSize (counted extractA.arguments) = 2 ∧
    Roles.argsSize (counted extractB.arguments) = 2 ∧
    Roles.argsSize (counted w.head) = 4 ∧
    Roles.argsSize (counted childC.arguments) = 2 := by decide +kernel

end Yulang.GeneralNominalProvenanceDeclarations
