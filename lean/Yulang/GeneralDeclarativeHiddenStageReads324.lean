import Yulang.GeneralDeclarativeHiddenStages324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenStageReads324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenStages324 (Stage old_source localRule root_ready' leaf_ready' no_recurs tested_root tested_leaf)
open GeneralDeclarativeHiddenReads324 (rootUses body_root body_child)
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeHiddenResolve324 (root_only child_only)
open GeneralDeclarativeExampleSource320 (leaf point)
open GeneralDeclarativeNFNode324 (Reads)
open GeneralDeclarativeNFHead324 (Scan produces)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeRecordWalk323 (closed_record)
open GeneralDeclarativeExactWalk323 (of_rigid)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeHead320 (Equation)
open CommonRoleOutermostResolver (All₂)

theorem scan_at (phase : Stage) : Scan phase.ordinary catalogue interpretation (point 0) raw rootUses := by
  refine ⟨root_bounds _ _,direct,normCode,?_,normal_compiles,?_⟩
  · exact literal (old_source phase (show (⟨0,direct⟩ : Equation) ∈ s0Rows from List.mem_cons_self))
  · exact closed_record (mode := .actual) (xs := [(7,.variable 3)]) (ys := [(7,.variable 0)])
      (.cons (of_rigid .capture) .nil) (by simp)

theorem read_parent (phase : Stage) : Reads phase.ordinary registry interpretation root parent names place := by
  refine ⟨.cons ⟨root_bounds _ _,produces (scan_at phase) ?_⟩ .nil,?_,?_,?_⟩
  · intro m _ item occurs
    cases List.mem_singleton.mp occurs
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

theorem read_child (phase : Stage) : Reads phase.ordinary registry interpretation child leaf leafNames place := by
  refine ⟨.cons ⟨root_bounds _ 3,?_⟩ .nil,fun _ _ => root_bounds _ 3,
    fun _ impossible => False.elim (List.not_mem_nil impossible),fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  refine ⟨[⟨3,.variable 3⟩],rfl,?_⟩
  intro row used m _
  cases List.mem_singleton.mp used
  exact eqv_refl (m 3).1

/-- The actual source can choose the parent from ordinary input facts
before either associated update. This is not a final dictionary result. -/
theorem selected_parent (phase : Stage) (completed : Nat → Prop) :
    localRule phase completed root (.selected parent.id [child]) := by
  refine .selected (root_ready' phase completed) (no_recurs phase completed _)
    ?_ ⟨⟨List.mem_cons_self,rfl⟩,tested_root phase completed⟩ ?_
    ⟨names,place,exact_child,read_parent phase,body_root⟩
  · rintro ⟨d,⟨vis,role⟩,block⟩
    cases root_only d vis role
    exact block (tested_root phase completed)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [root_only d vis role]

theorem selected_child (phase : Stage) (completed : Nat → Prop) :
    localRule phase completed child (.selected leaf.id []) := by
  refine .selected (leaf_ready' phase completed) (no_recurs phase completed _)
    ?_ ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,tested_leaf phase completed⟩ ?_
    ⟨leafNames,place,rfl,read_child phase,body_child⟩
  · rintro ⟨d,⟨vis,role⟩,block⟩
    cases child_only d vis role
    exact block (tested_leaf phase completed)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [child_only d vis role]

end Yulang.GeneralDeclarativeHiddenStageReads324
