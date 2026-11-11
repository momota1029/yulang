import Yulang.GeneralDeclarationDemands

/-!
# Role declaration examples from section 6.3

The examples use the same general declaration, pattern, and demand carriers.
Constructor names 0 and 1 stand for list and box; output names 0 and 1 stand
for out and item. No candidate registry is used to infer an unknown argument.
-/
namespace Yulang.GeneralDeclarationExamples

open GeneralDeclarationPatterns GeneralDeclarations GeneralDeclarationDemands

abbrev bareRole : Roles.RoleDecl := ⟨1, fun _ => none, by intros; contradiction⟩
abbrev binaryRole : Roles.RoleDecl := ⟨2, fun _ => none, by intros; contradiction⟩
abbrev outputRole (output : Nat) : Roles.RoleDecl :=
  ⟨1, fun name => if name = output then some none else none, by
    intro name rhs impossible
    split at impossible <;> cases impossible⟩
abbrev roles : Roles.RoleDecls := fun role =>
  if role = 1 then outputRole 0 else if role = 2 then outputRole 1
  else if role = 4 then binaryRole else bareRole

abbrev constructors : Constructors := fun name =>
  some ⟨if name = 0 ∨ name = 1 then [.type] else if name = 5 then [.type, .type] else [], name⟩

abbrev displayChild : Clause := ⟨10, 0, [.var 0], []⟩
abbrev display : Declaration := ⟨1, 0, [.app 0 [.var 0]], [displayChild], [], []⟩
abbrev itemEquation : Equation := ⟨21, 1, .var 1⟩
abbrev containerChild : Clause := ⟨20, 2, [.var 0], [itemEquation]⟩
abbrev outDefinition : Equation := ⟨22, 0, .app 0 [.var 1]⟩
abbrev itemBinder : OutputBinder := ⟨1, 20, 21⟩
abbrev wrap : Declaration := ⟨2, 1, [.app 0 [.var 0]], [containerChild], [outDefinition], [itemBinder]⟩

theorem display_checked : DeclarationChecked constructors roles display := by
  constructor
  · simp [Declaration.Signature, Clause.Signature, roles, bareRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact ⟨rfl, rfl⟩
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    unfold ConservativeSmaller
    decide +kernel
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact unary_descent 0 0

private theorem wrap_signature : wrap.Signature roles := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    exact ⟨none, rfl⟩
  · intro name body present
    by_cases zero : name = 0
    · subst name
      exact Or.inl ⟨outDefinition, by simp, rfl⟩
    · simp [roles, outputRole, zero] at present
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    refine ⟨rfl, ?_⟩
    intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    exact ⟨none, rfl⟩

theorem wrap_checked : DeclarationChecked constructors roles wrap := by
  constructor
  · exact wrap_signature
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames, variablesArgs, Pattern.variables]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact ⟨rfl, rfl⟩
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    unfold ConservativeSmaller
    decide +kernel
  · intro clause member
    have same := List.mem_singleton.mp member
    subst clause
    exact unary_descent 0 0

abbrev registry : Registry := ⟨constructors, roles, [display, wrap]⟩

theorem registry_checked : Checked registry := by
  refine ⟨by simp, ?_⟩
  intro declaration member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact display_checked
  · exact wrap_checked

abbrev showOutputChild : Clause := ⟨30, 3, [.var 1], []⟩
abbrev showOutput : Declaration :=
  ⟨3, 3, [.app 1 [.var 0]], [containerChild, showOutputChild], [], [itemBinder]⟩

theorem output_used_as_input_rejected :
    ¬ DeclarationChecked constructors roles showOutput :=
  output_input_rejected showOutput showOutputChild (by simp) 1
    (by simp [Declaration.outputNames]) (by simp [variablesArgs, Pattern.variables])

abbrev plainRecord : Pattern := .record 7 (.app 2 []) (.app 4 [])
abbrev shadowRecord : Pattern := .record 7 (.app 2 []) plainRecord
abbrev shadowChild : Clause := ⟨40, 0, [plainRecord], []⟩
abbrev shadowDeclaration : Declaration := ⟨4, 0, [shadowRecord], [shadowChild], [], []⟩

theorem hidden_padding_rejected :
    ¬ DeclarationChecked constructors roles shadowDeclaration := by
  intro checked
  have smaller := (checked.paterson shadowChild (by simp)).1
  have equal : counted shadowDeclaration.head = counted shadowChild.arguments := by decide +kernel
  rw [equal] at smaller
  exact Nat.lt_irrefl _ smaller

abbrev lateHead : List Pattern :=
  [.var 0, .variant 7 (.join (.app 5 [.app 2 [], .var 0]) (.app 5 [.var 0, .app 2 []]))]
abbrev lateChild : Clause := ⟨50, 4, [.var 0, .variant 7 (.app 5 [.var 0, .var 0])], []⟩
abbrev lateDeclaration : Declaration := ⟨5, 4, lateHead, [lateChild], [], []⟩

theorem capture_merge_signature : lateDeclaration.Signature roles := by
  simp [Declaration.Signature, Clause.Signature, roles, binaryRole]

theorem capture_merge_rejected :
    ¬ DeclarationChecked constructors roles lateDeclaration :=
  late_merge_rejected lateDeclaration lateChild (by simp) (fun _ => .app 2 [])
    (by decide +kernel)

abbrev wrapCapture : Capture := ⟨fun _ => (100, 101), fun _ => 200⟩
abbrev wrapAllocation : Allocation roles containerChild := ⟨fun _ => (300, 301), fun _ => 400⟩

theorem wrap_child_keeps_item :
    let child := emit 9 wrap containerChild (wrap_checked.signature.2.2.2 containerChild (by simp))
      wrapCapture wrapAllocation
    child.invocation = 9 ∧ child.declaration = 2 ∧ child.clause = 20 ∧
      child.demand.role = 2 ∧
      child.demand.arguments ⟨0, by simp [child, emit, childDemand, roles, outputRole]⟩ = (100, 101) ∧
      child.demand.outputs = [⟨1, 200⟩] ∧
      child.outputs = [⟨21, 1, .var 1, 200⟩] := by
  simp [emit, childDemand, inputInterval, outputTarget, normalize, Declaration.outputNames]

theorem nonadjacent_tag_grouped :
    normalize (.join (.join (.variant 7 (.app 2 [])) (.variant 8 (.app 3 [])))
      (.variant 7 (.app 2 []))) =
    normalize (.join (.variant 7 (.app 2 [])) (.variant 8 (.app 3 []))) := by
  simp [normalize, merge, variantRow, rowPattern, mergePayload,
    Variants.Merged.normalize, Variants.Merged.Raw.insert]

end Yulang.GeneralDeclarationExamples
