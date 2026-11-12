import Yulang.GeneralNominalDemandMerging
import Yulang.GeneralDeclarationExamples

/-! Local associated determination does not assert registry-wide overlap
coherence. Both declarations below pass Checked; their different outputs must
not be treated as the outputs of one common dictionary interpretation. -/
namespace Yulang.GeneralNominalAssociatedDeterminationScope

open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationExamples

abbrev first : Declaration := ⟨50,1,[.app 2 []],[],[⟨500,0,.app 2 []⟩],[]⟩
abbrev last : Declaration := ⟨51,1,[.app 2 []],[],[⟨501,0,.app 3 []⟩],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[first,last]⟩

private theorem constant_checked (key equation rhs : Nat) (notList : rhs ≠ 0) (notBox : rhs ≠ 1) (notPair : rhs ≠ 5) :
    DeclarationChecked constructors roles ⟨key,1,[.app 2 []],[],[⟨equation,0,.app rhs []⟩],[]⟩ := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro output member
      have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨⟨equation,0,.app rhs []⟩,by simp,rfl⟩
      · simp [roles,outputRole,zero] at present
    · intro clause member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,notList,notBox,notPair]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem overlapping_registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  rcases List.mem_cons.mp member with rfl | member
  · exact constant_checked 50 500 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · have same := List.mem_singleton.mp member; subst declaration
    exact constant_checked 51 501 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem same_head_different_associated :
    first.normalHead = last.normalHead ∧
      (normalize (first.associated[0]'(by decide +kernel)).rhs).subst (fun name => .var name) ≠
        (normalize (last.associated[0]'(by decide +kernel)).rhs).subst (fun name => .var name) := by
  exact ⟨rfl,by decide +kernel⟩

end Yulang.GeneralNominalAssociatedDeterminationScope
