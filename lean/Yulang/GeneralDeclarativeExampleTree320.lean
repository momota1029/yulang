import Yulang.GeneralDeclarativeExampleRead320
import Yulang.GeneralDeclarativeNamedTree320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeExampleTree320
open GeneralDeclarationExamples (wrap containerChild itemEquation)
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeExampleRead320 (root_recipe leaf_recipe root_prepared root_only leaf_only)
open GeneralDeclarativeEvidence320 (Produces Evidence classify_sound)
open GeneralDeclarativeAssembly320 (chosen_sound prepared_sound)
open GeneralDeclarativeLeaf320 (LeafSelection)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Demand sourceValue)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (Supplies)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Frontier Dictionary Tree Classify All₂ Resolves Summarizes Result)

theorem leaf_choice : LeafSelection state registry interp child leaf.id leaf [0] := by
  refine ⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,rfl,leaf_only,rfl,by decide +kernel,
    rfl,rfl,?_,?_,?_⟩
  · intro arg present
    cases List.mem_singleton.mp present
    exact ⟨.int,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · intro arg present
    cases List.mem_singleton.mp present
    exact point_bounds 3
  · intro out present
    cases List.mem_singleton.mp present
    exact ⟨.explicit association,.variable 0,rfl,rfl,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- The exact two positive local frontiers of this checked isolated
source example. No general negative outcome or solver step is claimed. -/
inductive FixtureLocal : Demand → Frontier Demand → Prop where
  | root (sole : ∀ d ∈ registry.declarations, d.role = root.role → d = wrap) :
      FixtureLocal root (.selected wrap.id [child])
  | child (picked : LeafSelection state registry interp child leaf.id leaf [0]) :
      FixtureLocal child (.selected leaf.id [])

theorem local_producer : Produces state registry interp FixtureLocal := by
  intro d key kids derived
  cases derived with
  | root => exact root_recipe
  | child => exact leaf_recipe

abbrev dictionary : Dictionary := .node wrap.id [.node leaf.id []]
abbrev diagnostic : Tree := .selected wrap.id [.selected leaf.id []]

theorem resolves : Resolves FixtureLocal root diagnostic :=
  .selected (.root root_only) (.cons (.selected (.child leaf_choice) .nil) .nil)

theorem completes : Summarizes diagnostic (.selected dictionary) :=
  .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem accepted : Classify FixtureLocal root (.selected dictionary) :=
  ⟨diagnostic,resolves,completes⟩

theorem evidence (m : Assignment) (valid : Models state m) : Evidence registry interp m root dictionary :=
  classify_sound checked local_producer m valid accepted

theorem requested_item_link (m : Assignment) (valid : Models state m) :
    ∃ chosen values body,
      chosen.id = leaf.id ∧ chosen ∈ registry.declarations ∧ chosen.role = containerChild.role ∧
      (1 : Nat) = itemEquation.name ∧ Supplies registry.roles chosen 1 body ∧
      Equivalent (sourceValue registry.constructors interp capture m itemEquation.rhs)
        (sourceValue registry.constructors interp (bodyCapture child values body) m (bodyPattern body)) := by
  have read := prepared_sound checked root_prepared m valid
  have kids : All₂ (Evidence registry interp m) [child] [.node leaf.id []] :=
    .cons (.node (chosen_sound checked leaf_recipe m valid) .nil) .nil
  exact GeneralDeclarativeNamedTree320.linked_output read kids (i := 0) (j := 0) rfl rfl rfl rfl
    (show child.outputs[0]? = some ⟨1,5⟩ from rfl)

theorem inhabited : Models state model ∧ Evidence registry interp model root dictionary :=
  ⟨valid,evidence model valid⟩

end Yulang.GeneralDeclarativeExampleTree320
