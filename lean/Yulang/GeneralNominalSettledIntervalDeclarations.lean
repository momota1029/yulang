import Yulang.GeneralNominalFreshPumpDeclarations

/-! A two-role structural interval pump. The leaf W has no requirements.
Its anchor and wrapped output share one requested target in the P emission. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSettledIntervalDeclarations
open GeneralDeclarationPatterns GeneralDeclarations GeneralDeclarationDemands

abbrev bareRole := GeneralNominalProvenanceDeclarations.bareRole
abbrev roles : Roles.RoleDecls
  | 0 => bareRole 2
  | 1 => ⟨2,fun name => if name < 3 then some none else none,by
      intro name rhs impossible; split at impossible <;> cases impossible⟩
  | _ => bareRole 0
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev tick (a : Pattern) : Pattern := .variant 0 a
abbrev wrapChild : Clause := ⟨10,1,[tick (.var 0),.var 1],
  [⟨100,0,.var 2⟩,⟨101,1,.var 2⟩,⟨102,2,.var 3⟩]⟩
abbrev recurChild : Clause := ⟨11,0,[tick (.var 0),.var 1],[]⟩
abbrev p : Declaration := ⟨0,0,[tick (tick (.var 0)),.var 1],
  [wrapChild,recurChild],[],[⟨2,10,100⟩,⟨3,10,102⟩]⟩
abbrev w : Declaration := ⟨1,1,[tick (.var 0),.var 1],[],
  [⟨200,0,.var 0⟩,⟨201,1,tick (.var 1)⟩,⟨202,2,.var 1⟩],[]⟩

private theorem p_stable (clause : Clause) (member : clause ∈ p.requirements) :
    StableSmaller p.head clause.arguments := by
  simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals
    intro capture
    constructor
    · simp only [tick,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp only [tick,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
        encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
      omega

theorem p_checked : DeclarationChecked constructors roles p := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,bareRole,
      GeneralNominalProvenanceDeclarations.bareRole,p,wrapChild,recurChild]
  · simp [Declaration.Identified,Declaration.outputNames,p,wrapChild,recurChild]
  · simp [Declaration.Produced,p,wrapChild,recurChild]
  · simp [Declaration.OutputOnly,Declaration.outputNames,p,wrapChild,recurChild,
      tick,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,p,wrapChild,recurChild,
      tick,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      p,wrapChild,recurChild,tick]
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · exact p_stable

theorem w_checked : DeclarationChecked constructors roles w := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,w]
    intro name h
    omega
  · simp [Declaration.Identified,Declaration.outputNames,w]
  · simp [Declaration.Produced,w]
  · simp [Declaration.OutputOnly,Declaration.outputNames,w]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,w,
      tick,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,w,tick]
  all_goals intro _ impossible; cases impossible

abbrev registry : Registry := ⟨constructors,roles,[p,w]⟩

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration present
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  · exact p_checked
  · exact w_checked

theorem shared_anchor (capture : Capture) (allocate : Nat → Nat) :
    outputTarget p capture allocate ⟨100,0,.var 2⟩ = capture.outputs 2 ∧
    outputTarget p capture allocate ⟨101,1,.var 2⟩ = capture.outputs 2 ∧
    outputTarget p capture allocate ⟨102,2,.var 3⟩ = capture.outputs 3 := by
  simp [outputTarget,normalize,Declaration.outputNames,p]

def bind (a b : Pattern) : Nat → Pattern | 0 => a | _ => b

theorem recursive_emission (a b : Pattern) :
    substArgs (bind (tick a) b) recurChild.arguments = substArgs (bind a b) p.head := rfl

end Yulang.GeneralNominalSettledIntervalDeclarations
