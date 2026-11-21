import Yulang.GeneralDeclarativeAggregateProbe324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregateResolve324
open GeneralDeclarativeAggregateFixture324
open GeneralDeclarativeAggregateReads324 (childNames root_reads child_reads dict every_new_model)
open GeneralDeclarativeAggregateProbe324 (tests no_recurs parent_matches parent_ready child_matches)
open GeneralDeclarativeRepeatedSource323 (goal parent child registry checked)
open GeneralDeclarativeRepeatedResolve323 (parent_only)
open GeneralDeclarativeRepeatedReads323 (place)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeNFComplete324 (ReadBack)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Classify)

def generates (d : Demand) (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ names placement, children impl names placement = kids ∧
    ReadBack newState registry interp d impl names placement ∧ BodyCoverage registry interp d impl

abbrev localRule (complete : Nat → Prop) :=
  Local newState registry interp (support complete) (tests complete) generates

theorem child_only (impl) (vis : impl ∈ registry.declarations) (role : impl.role = emitted.role) :
    impl = child := by
  rcases List.mem_cons.mp vis with h|later
  · cases h
    cases role
  · exact List.mem_singleton.mp later

theorem root_selection (complete : Nat → Prop) :
    localRule complete goal (.selected parent.id [emitted]) := by
  refine .selected (parent_ready complete) (no_recurs complete _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,parent_matches complete⟩ ?_
    ⟨actualNames,place,exact_child,root_reads,fun _ none => False.elim (List.not_mem_nil none)⟩
  · rintro ⟨impl,⟨visible,role⟩,blocked⟩
    cases parent_only impl visible role
    exact blocked (parent_matches complete)
  · rintro impl ⟨⟨visible,role⟩,_⟩
    rw [parent_only impl visible role]

theorem child_selection (complete : Nat → Prop) : localRule complete emitted (.selected child.id []) := by
  refine .selected (child_ready complete) (no_recurs complete _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches complete⟩ ?_
    ⟨childNames,place,rfl,child_reads,fun _ none => False.elim (List.not_mem_nil none)⟩
  · rintro ⟨impl,⟨visible,role⟩,blocked⟩
    cases child_only impl visible role
    exact blocked (child_matches complete)
  · rintro impl ⟨⟨visible,role⟩,_⟩
    rw [child_only impl visible role]

theorem selected (complete : Nat → Prop) : Classify (localRule complete) goal (.selected dict) :=
  ⟨.selected parent.id [.selected child.id []],
    .selected (root_selection complete) (.cons (.selected (child_selection complete) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- This is the actually generated child, with aggregated endpoints
(33,34) and the first genuine center (3), not the older point fixture. -/
theorem full_result : Classify (localRule (fun _ => False)) goal (.selected dict) ∧
    (∃ model, Models newState model) ∧ ∀ m, Models newState m → Evidence registry interp m goal dict :=
  ⟨selected _,inhabited,every_new_model⟩

end Yulang.GeneralDeclarativeAggregateResolve324
