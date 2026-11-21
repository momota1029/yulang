import Yulang.GeneralDeclarativeClauseTransport325
import Yulang.GeneralDeclarativeNamedAliasResolve325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeReplayFixture325
open GeneralDeclarativeNamedAliasState325
open GeneralDeclarativeNamedAliasResolve325 (base current_root)
open GeneralDeclarativeHiddenWhere324 (root parent checked place registry clause rhs)
open GeneralDeclarativeHiddenDecl324 (raw normCode normal_compiles empty catalogue interpretation)
open GeneralDeclarativeHiddenState324 (direct)
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append)
open GeneralDeclarativeReplayNames325 (Joint replay)
open GeneralDeclarativeClauseTransport325 (At read_reused)
open GeneralDeclarativeDerivedSource325 (ordinary_rules)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeNFEmit324 (Read)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeTermWalk322 (Walk Occurrence)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNormalizeAssoc324 (row_iff)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonRoleOutermostResolver (All₂)

abbrev row : Equation := ⟨65,.variable 3⟩
abbrev state := appendFacts ordinary [row]
abbrev before := sourceNames parent place base
abbrev after := sourceNames parent place (fun _ => point 65)
abbrev newBody : Expr := .record 7 (.variable 65) empty

theorem new_alias : Alias state 65 3 := .forward (List.mem_append_right _ List.mem_cons_self)

theorem common_head : ∀ p ∈ parent.head, Joint state catalogue interpretation before.input after.input p := by
  intro p here
  cases List.mem_singleton.mp here
  let occurrence : Occurrence := ⟨0,.actual,.variable 3⟩
  refine ⟨direct,normCode,[occurrence],normal_compiles,.record .capture (.primitive .nil),?_,?_⟩
  · intro o seen
    cases List.mem_singleton.mp seen
    exact .refl _
  · intro o seen
    cases List.mem_singleton.mp seen
    exact .congruent (.variable (.backward (List.mem_append_right _ List.mem_cons_self)))

theorem same_where_targets : All₂ (fun a b : GeneralDeclarativeDemand320.Demand => a.outputs = b.outputs)
    (children parent before place) (children parent after place) := .cons rfl .nil

theorem prior : StableUnder state (SourceEquation registry interpretation root parent before.input) := by
  have original := (ordinary_rules checked List.mem_cons_self (current_root (fun _ => False))).2
  exact GeneralDeclarativeOutputIdentity324.keep_old_rules (fun m h => ((model_append m).mp h).1) original

theorem fixed_root_read : Entails state ⟨6,.variable 65⟩ := by
  have coherent (resolved : Nat → Capture) :
      GeneralDeclarativeEmissionOutputs322.Agree parent (sourceNames parent place resolved) :=
    GeneralDeclarativeProducedNames325.coherent _ _ _
  have joined := replay checked List.mem_cons_self common_head (coherent base)
    (coherent (fun _ => point 65)) same_where_targets prior
  exact stable_exact.mp joined _ ((row_iff checked List.mem_cons_self).mpr
    ⟨⟨0,6⟩,List.mem_cons_self,rfl⟩)

theorem changed_rhs_from_old_row : At state 55 newBody := by
  refine ⟨54,direct,?_,?_,.record (.variable ?_) (.primitive .nil)⟩
  · exact .forward (List.mem_append_left _ (show (⟨55,.variable 54⟩ : Equation) ∈ rows by simp [rows]))
  · exact List.mem_append_left _ (show (⟨54,direct⟩ : Equation) ∈ rows by simp [rows])
  · exact .backward (List.mem_append_right _ List.mem_cons_self)

theorem actual_reused_where : Read state registry interpretation parent clause after
    (place.compound clause) (place.targets clause) := by
  apply read_reused (codes := [.variable 0]) rfl
  · intro n pat expr has _ compound
    cases List.mem_singleton.mp (List.mem_of_getElem? has)
    exact False.elim (compound 0 rfl)
  · intro eq here
    cases List.mem_singleton.mp here
    exact ⟨normCode,rfl,fun _ => changed_rhs_from_old_row⟩

theorem possible : Models state assignment :=
  (model_append _).mpr ⟨populated,fun _ seen => by
    cases List.mem_singleton.mp seen
    exact eqv_refl _⟩

theorem new_readback (done : Nat → Prop) :
    GeneralDeclarativeNFComplete324.ReadBack state registry interpretation root parent after place := by
  let p := GeneralDeclarativeOutputOrigins323.emit (sources done) 9 [row]
  have trace := GeneralDeclarativeOrdinaryIncrease325.supported_trace
    (two := p) (GeneralDeclarativeOrdinaryIncrease325.append ordinary [row])
    (GeneralDeclarativeFrameIncrease325.old_support_after (sources done) [row] 9)
    (GeneralDeclarativeNamedAliasProbe325.head_trace done .actual)
  refine ⟨.cons ⟨GeneralDeclarativeHiddenProbe324.root_bounds state 0,?_⟩ .nil,?_,?_,?_⟩
  · apply GeneralDeclarativeHeadFrame325.each (support := p) (GeneralDeclarativeHiddenProbe324.root_bounds state 0)
    refine .actual normal_compiles trace ?_
    intro o belongs
    cases List.mem_singleton.mp belongs
    exact .congruent (.variable (.backward (List.mem_append_right _ List.mem_cons_self)))
  · intro key found
    change key ∈ [0] at found
    cases List.mem_singleton.mp found
    exact GeneralDeclarativeHiddenProbe324.root_bounds state 65
  · exact GeneralDeclarativeProducedNames325.coherent _ _ _
  · intro c used
    cases List.mem_singleton.mp used
    exact actual_reused_where

theorem source_compiles_after :
    GeneralDeclarativeCompileLists321.Result state
      (GeneralDeclarativeNFComplete324.facts registry interpretation after.input parent root
        (children parent after place)) := by
  have visible : parent ∈ registry.declarations := List.mem_cons_self
  have coverage := (ordinary_rules checked visible (current_root (fun _ => False))).1
  have coherent (resolved : Nat → Capture) :
      GeneralDeclarativeEmissionOutputs322.Agree parent (sourceNames parent place resolved) :=
    GeneralDeclarativeProducedNames325.coherent _ _ _
  have rules := replay checked visible common_head (coherent base)
    (coherent (fun _ => point 65)) same_where_targets prior
  exact GeneralDeclarativeNFComplete324.produces checked visible rfl
    GeneralDeclarativeNamedAliasResolve325.declared coverage (new_readback (fun _ => False)) rules

end Yulang.GeneralDeclarativeReplayFixture325
