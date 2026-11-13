import Yulang.GeneralNominalProvenanceDeclarations

/-! A checked accumulator pump. The middle output names the inner constructor
so that its value has an existing source identity for certified observation.
The output binders never occur in unnamed child arguments. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalFreshPumpDeclarations
open GeneralDeclarationPatterns GeneralDeclarations GeneralDeclarationDemands

abbrev bareRole := GeneralNominalProvenanceDeclarations.bareRole
abbrev outputRole := GeneralNominalProvenanceDeclarations.outputRole
abbrev roles : Roles.RoleDecls
  | 0 => bareRole 3
  | 1 => ⟨3, fun name => if name = 0 ∨ name = 1 then some none else none, by
      intro name rhs impossible; split at impossible <;> cases impossible⟩
  | 2 => outputRole 2 0
  | 3 => outputRole 1 0
  | _ => bareRole 0
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev list (a : Pattern) : Pattern := .app 0 [a]

abbrev extractChild : Clause := ⟨10,3,[list (.var 0)],[⟨100,0,.var 3⟩]⟩
abbrev wrapChild : Clause := ⟨11,1,[list (.var 0),.var 1,.var 2],
  [⟨110,0,.var 3⟩,⟨111,1,.var 4⟩]⟩
abbrev recurChild : Clause := ⟨12,0,[list (.var 0),list (.var 1),.var 2],[]⟩
abbrev p : Declaration := ⟨0,0,[list (list (list (.var 0))),.var 1,.var 2],
  [extractChild,wrapChild,recurChild],[],[⟨3,10,100⟩,⟨4,11,111⟩]⟩
abbrev blockedChild : Clause := ⟨20,2,[.var 1,.var 2],[⟨200,0,.var 3⟩]⟩
abbrev w : Declaration := ⟨1,1,[list (.var 0),.var 1,.var 2],[blockedChild],
  [⟨201,0,list (list (.var 3))⟩,⟨202,1,list (.var 3)⟩],[⟨3,20,200⟩]⟩
abbrev c : Declaration := ⟨2,2,[.var 0,list (.app 2 [])],[],[⟨301,0,.app 2 []⟩],[]⟩
abbrev extract : Declaration := ⟨3,3,[list (.var 0)],[],[⟨401,0,.var 0⟩],[]⟩

private theorem p_stable (clause : Clause) (member : clause ∈ p.requirements) :
    StableSmaller p.head clause.arguments := by
  simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    intro capture
    constructor
    · simp only [list,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp only [list,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
      omega

theorem p_checked : DeclarationChecked constructors roles p := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,bareRole,outputRole,
      GeneralNominalProvenanceDeclarations.bareRole,GeneralNominalProvenanceDeclarations.outputRole,
      p,extractChild,wrapChild,recurChild]
  · simp [Declaration.Identified,Declaration.outputNames,p,extractChild,wrapChild,recurChild]
  · simp [Declaration.Produced,p,extractChild,wrapChild,recurChild]
  · simp [Declaration.OutputOnly,Declaration.outputNames,p,extractChild,wrapChild,recurChild,
      list,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,p,extractChild,wrapChild,recurChild,
      list,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors,
      p,extractChild,wrapChild,recurChild,list]
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · exact p_stable

theorem w_checked : DeclarationChecked constructors roles w := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,outputRole,
      GeneralNominalProvenanceDeclarations.outputRole,w,blockedChild]
  · simp [Declaration.Identified,Declaration.outputNames,w,blockedChild]
  · simp [Declaration.Produced,w,blockedChild]
  · simp [Declaration.OutputOnly,Declaration.outputNames,w,blockedChild,list,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,w,blockedChild,
      list,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDeclarationExamples.constructors,w,blockedChild,list]
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
    intro capture
    constructor
    · simp only [list,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp only [list,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
      omega

theorem c_checked : DeclarationChecked constructors roles c := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,outputRole,
      GeneralNominalProvenanceDeclarations.outputRole,c]
  · simp [Declaration.Identified,Declaration.outputNames,c]
  · simp [Declaration.Produced,c]
  · simp [Declaration.OutputOnly,Declaration.outputNames,c]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,c,
      list,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDeclarationExamples.constructors,c,list]
  all_goals intro clause impossible; cases impossible

theorem extract_checked : DeclarationChecked constructors roles extract := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,outputRole,
      GeneralNominalProvenanceDeclarations.outputRole,extract]
  · simp [Declaration.Identified,Declaration.outputNames,extract]
  · simp [Declaration.Produced,extract]
  · simp [Declaration.OutputOnly,Declaration.outputNames,extract]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,extract,
      list,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDeclarationExamples.constructors,extract,list]
  all_goals intro clause impossible; cases impossible

abbrev registry : Registry := ⟨constructors,roles,[p,w,c,extract]⟩

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact p_checked
  · exact w_checked
  · exact c_checked
  · exact extract_checked

/-- The actual emitter joins Extract and W without an equation supplied by P.
It also reserves the intermediate nominal value as a second named output. -/
theorem shared_outputs (capture : Capture)
    (ea : Allocation roles extractChild) (wa : Allocation roles wrapChild) :
    (childDemand p extractChild (p_checked.signature.2.2.2 _ (by simp)) capture ea).outputs =
      [⟨0,capture.outputs 3⟩] ∧
    (childDemand p wrapChild (p_checked.signature.2.2.2 _ (by simp)) capture wa).outputs =
      [⟨0,capture.outputs 3⟩,⟨1,capture.outputs 4⟩] := by
  simp [childDemand,outputTarget,Declaration.outputNames,normalize]

/-- These are the retained patterns of the real child emitter. -/
theorem recursive_emission (invocation : Nat) (capture : Capture)
    (allocation : Allocation roles recurChild) :
    ((emit invocation p recurChild (p_checked.signature.2.2.2 _ (by simp)) capture allocation).inputs.map
      InputRequest.pattern) = [list (.var 0),list (.var 1),.var 2] := by
  rfl

end Yulang.GeneralNominalFreshPumpDeclarations
