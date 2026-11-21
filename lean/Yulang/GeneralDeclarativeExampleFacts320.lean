import Yulang.GeneralDeclarativeCompilerTree320
import Yulang.GeneralDeclarativeExampleTree320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15500
set_option maxHeartbeats 4500000
namespace Yulang.GeneralDeclarativeExampleFacts320
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeExampleRead320 (root_head_read childCapture)
open GeneralDeclarativeExampleTree320 (FixtureLocal dictionary accepted)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEntailment320 (Entails Holds BatchRecipe literal)
open GeneralDeclarativeNodeFacts320 (nodeFacts)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralDeclarativeNormalized320 (center_sound)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev rootFacts : List Equation :=
  [⟨1,nApp 3⟩,⟨3,.variable 3⟩,⟨3,.variable 3⟩,⟨3,.variable 3⟩,
    ⟨5,.variable 5⟩,⟨6,nApp 5⟩]

abbrev leafFacts : List Equation := [⟨3,.variable 3⟩,⟨5,.variable 3⟩]

theorem root_batch : nodeFacts registry interp capture wrap root [child] = some rootFacts := rfl
theorem leaf_batch : nodeFacts registry interp childCapture leaf child [] = some leafFacts := rfl

theorem reflexive_eq (name : Nat) : Entails state ⟨name,.variable name⟩ :=
  fun m _ => eqv_refl (m name).1

theorem center_consequence : Entails state ⟨1,nApp 3⟩ := by
  intro m valid
  exact center_sound root_head_read m valid

/-- The exact batch includes an equation not literally listed at the root
center. It's nevertheless an ordinary consequence of the original facts. -/
theorem root_settled : ∀ row ∈ rootFacts, Entails state row := by
  intro eq used
  simp only [rootFacts,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl|rfl|rfl
  · exact center_consequence
  · exact reflexive_eq 3
  · exact reflexive_eq 3
  · exact reflexive_eq 3
  · exact reflexive_eq 5
  · exact literal (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

theorem leaf_settled : ∀ row ∈ leafFacts, Entails state row := by
  intro row used
  rcases List.mem_cons.mp used with rfl|tail
  · exact reflexive_eq 3
  · cases List.mem_singleton.mp tail
    exact literal (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem batch_root_recipe : BatchRecipe state registry interp root wrap.id [child] := by
  refine ⟨wrap,capture,rootFacts,rfl,List.mem_cons_self,?_,?_,root_batch,root_settled⟩
  · intro n member
    change n ∈ [0] at member
    cases List.mem_singleton.mp member
    exact point_bounds 3
  · intro a member
    cases List.mem_singleton.mp member
    exact input_bounds

theorem batch_leaf_recipe : BatchRecipe state registry interp child leaf.id [] := by
  refine ⟨leaf,childCapture,leafFacts,rfl,List.mem_cons_of_mem _ (List.mem_singleton_self _),
    fun _ _ => point_bounds 3,?_,leaf_batch,leaf_settled⟩
  intro a used
  cases List.mem_singleton.mp used
  exact point_bounds 3

theorem compiler_produces : Compiles state registry interp FixtureLocal := by
  intro d key kids chosen
  cases chosen with
  | root => exact .inr batch_root_recipe
  | child => exact .inr batch_leaf_recipe

theorem compiled_evidence (m : Assignment) (valid : Models state m) :
    Evidence registry interp m root dictionary :=
  compile_classify checked compiler_produces m valid accepted

end Yulang.GeneralDeclarativeExampleFacts320
