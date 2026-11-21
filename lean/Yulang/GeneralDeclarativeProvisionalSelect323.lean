import Yulang.GeneralDeclarativeProvisionalFixture323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProvisionalSelect323
open GeneralDeclarativeProvisionalFixture323
open GeneralDeclarativeEmissionFixture322 (names place actual_names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeExampleSource320 (root child registry interp leaf point checked)
open GeneralDeclarativeExampleRead320 (root_only leaf_only)
open GeneralDeclarativeExampleTree320 (diagnostic dictionary completes)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativePriority321 (Local Blocked Survives)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Classify)

/-- Keeps the actual source emitter. In this test the capture is fixed by
the two branch heads; this relation deliberately checks only emission,
not stability of all requested ordinary equations. -/
def syntactic (d : GeneralDeclarativeDemand320.Demand) (decl : Declaration)
    (kids : List GeneralDeclarativeDemand320.Demand) : Prop :=
  (d = root ∧ decl = wrap ∧ kids = children wrap names place) ∨
  (d = child ∧ decl = leaf ∧ kids = children leaf ⟨fun _ => point 3,fun _ => 3⟩ place)

abbrev localRule := Local before registry interp inputSupport test syntactic

theorem parent_selected : localRule root (.selected wrap.id [child]) := by
  refine .selected readyRoot (no_recurs _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,root_matches⟩ ?_ ?_
  · rintro ⟨decl,⟨visible,role⟩,unknown⟩
    cases root_only decl visible role
    exact unknown root_matches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [root_only decl visible role]
  · exact .inl ⟨rfl,rfl,actual_names.symm⟩

theorem child_selected : localRule child (.selected leaf.id []) := by
  refine .selected readyChild (no_recurs _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,leaf_matches⟩ ?_ (.inr ⟨rfl,rfl,rfl⟩)
  · rintro ⟨decl,⟨visible,role⟩,unknown⟩
    cases leaf_only decl visible role
    exact unknown leaf_matches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [leaf_only decl visible role]

theorem before_tree : Classify localRule root (.selected dictionary) :=
  ⟨diagnostic,.selected parent_selected (.cons (.selected child_selected .nil) .nil),completes⟩

end Yulang.GeneralDeclarativeProvisionalSelect323
