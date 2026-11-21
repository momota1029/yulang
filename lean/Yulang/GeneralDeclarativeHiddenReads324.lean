import Yulang.GeneralDeclarativeHiddenProbe324
import Yulang.GeneralDeclarativeNFResolve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenReads324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeExampleSource320 (leaf point association)
open GeneralDeclarativeNFNode324 (Reads BodyCoverage)
open GeneralDeclarativeNFHead324 (Scan produces)
open GeneralDeclarativeNFResolve324 (Generates)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeExactWalk323 (of_rigid)
open GeneralDeclarativeRecordWalk323 (closed_record)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)

abbrev rootUses : List Occurrence := [⟨0,.actual,.variable 3⟩]

theorem root_scan : Scan final catalogue interpretation (point 0) raw rootUses := by
  refine ⟨root_bounds _ _, direct,normCode,?_,normal_compiles,?_⟩
  · exact literal (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  · have read := closed_record (mode := .actual)
      (xs := [(7,.variable 3)]) (ys := [(7,.variable 0)])
      (.cons (of_rigid .capture) .nil) (by simp)
    exact read

theorem body_root : BodyCoverage registry interpretation root parent := by
  intro asked seen body supply
  cases List.mem_singleton.mp seen
  cases supply with
  | explicit eq present _ =>
    cases List.mem_singleton.mp present
    exact trivial
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

theorem body_child : BodyCoverage registry interpretation child leaf := by
  intro asked seen body supply
  cases List.mem_singleton.mp seen
  cases supply with
  | explicit eq present _ =>
    cases List.mem_singleton.mp present
    exact trivial
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

theorem declared_root : Declared registry root := by
  intro request used
  cases List.mem_singleton.mp used
  exact ⟨none,rfl⟩

theorem declared_child : Declared registry child := by
  intro request used
  cases List.mem_singleton.mp used
  exact ⟨none,rfl⟩

theorem root_reads : Reads final registry interpretation root parent names place := by
  refine ⟨.cons ⟨root_bounds _ _,produces root_scan ?_⟩ .nil,?_,?_,?_⟩
  · intro m _ entry seen
    cases List.mem_singleton.mp seen
    exact eqv_refl (m 3).1
  · intro mentioned found
    rw [hidden_not_in_scope.1] at found
    cases List.mem_singleton.mp found
    exact root_bounds _ 3
  · intro name belongs
    change name ∈ [1] at belongs
    cases List.mem_singleton.mp belongs
    rfl
  · intro clause there
    cases List.mem_singleton.mp there
    constructor
    · refine ⟨[.variable 0],.cons rfl .nil,?_⟩
      intro idx pat code hp hc nonvar
      cases List.mem_singleton.mp (List.mem_of_getElem? hp)
      exact False.elim (nonvar 0 rfl)
    · intro eq belongs
      cases List.mem_singleton.mp belongs
      refine ⟨.variable 1,.variable 1,rfl,rfl,?_⟩
      intro impossible
      exact False.elim (impossible ⟨1,rfl,List.mem_cons_self⟩)

theorem leaf_reads : Reads final registry interpretation child leaf leafNames place := by
  refine ⟨.cons ⟨root_bounds _ 3,?_⟩ .nil,fun _ _ => root_bounds _ 3,?_ ,?_⟩
  · refine ⟨[⟨3,.variable 3⟩],rfl,?_⟩
    intro e occurs m _
    cases List.mem_singleton.mp occurs
    exact eqv_refl (m 3).1
  · intro _ empty
    cases empty
  · intro _ empty
    cases empty

theorem root_generated : Generates final registry interpretation root parent [child] :=
  ⟨names,place,exact_child,root_reads,body_root⟩

theorem child_generated : Generates final registry interpretation child leaf [] :=
  ⟨leafNames,place,rfl,leaf_reads,body_child⟩

end Yulang.GeneralDeclarativeHiddenReads324
