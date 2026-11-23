import Yulang.GeneralDeclarativeWitnessAuthoredProjection358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessProjectionRule358
open GeneralDeclarativeWitnessDeclaredState357 (Current ModelsCurrent Views WrittenBody authoredRegistry)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source Recipe Projected BoundsIn original_nonpoint_projection)
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked roleView roleView_span)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (All₂ Frontier Tree Dictionary Result Classify Resolves Summarizes)
open GeneralDeclarationPatterns (normalizeArgs)

structure Selected (a : Source) (s : Current) (d : Demand) (impl : Declaration) (kids : List Demand) where
  read : Recipe
  backed : Projected a s.ordinary read
  single : (roleView s d.role).declarations = [impl]
  actual : d.arguments = [read.outer]
  binder : Nat
  normalized : normalizeArgs impl.head = [.variant read.tag (.var binder)]
  body : WrittenBody s d impl [(binder,read.inner)] kids

inductive Rule (a : Source) (s : Current) : Demand → Frontier Demand → Prop where
  | prior : GeneralDeclarativeWitnessClassifyVariance357.Rule s d result → Rule a s d result
  | projection (selected : Selected a s d impl kids) : Rule a s d (.selected impl.id kids)

inductive LocalEvidence (a : Source) (s : Current) (m : Assignment) (v : Views) :
    Demand → Nat → List Demand → Prop where
  | prior : GeneralDeclarativeWitnessClassifyVariance357.LocalEvidence s m v d key kids →
      LocalEvidence a s m v d key kids
  | projection (selected : Selected a s d impl kids) :
      GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered s.environment impl →
      BoundsIn m selected.read →
      selected.body.finished.fixed.map Equation.left = d.outputs.map GeneralSourceState.Output.target →
      (∀ row ∈ selected.body.finished.fixed,Holds m row) →
      LocalEvidence a s m v d impl.id kids

theorem selected_visible {a s d impl kids} (selection : Selected a s d impl kids) :
    impl ∈ (authoredRegistry s).declarations ∧ impl.role = d.role :=
  (roleView_span s d.role impl).mp (by rw [selection.single]; exact List.mem_cons_self)

theorem root_declared {a s d impl kids} (selection : Selected a s d impl kids) (checked : SourceChecked s) :
    Declared (authoredRegistry s) d := by
  have visible := selected_visible selection
  have legal := checked.2 impl visible.1
  exact GeneralDeclarativeWitnessRootDeclared357.written_root_declared selection.body
    legal.signature legal.identified.2.2.1 visible.2

theorem local_sound {a s} (checked : SourceChecked s) (cover : Coverage s.environment)
    {d key kids} (selected : Rule a s d (.selected key kids)) (declared : Declared (authoredRegistry s) d)
    (m : Assignment) (v : Views) (fit : ModelsCurrent s m v) :
    LocalEvidence a s m v d key kids ∧ ∀ child ∈ kids,Declared (authoredRegistry s) child := by
  cases selected with
  | prior seen =>
    have ordinary := GeneralDeclarativeWitnessClassifyVariance357.local_sound checked cover seen declared m v fit
    exact ⟨.prior ordinary.1,ordinary.2⟩
  | projection selected =>
    have visible := selected_visible selected
    have legal := checked.2 _ visible.1
    have rows := GeneralDeclarativeWitnessDeclaredState357.output_meaning selected.body m fit.1
    exact ⟨.projection selected (cover.1 _ visible.1) (original_nonpoint_projection selected.backed m fit.1)
      rows.1 rows.2,GeneralDeclarativeWitnessDeclaredState357.body_declared selected.body legal.signature⟩

inductive Evidence (a : Source) (s : Current) (m : Assignment) (v : Views) : Demand → Dictionary → Prop where
  | node :
      LocalEvidence a s m v d key kids →
      All₂ (Evidence a s m v) kids dicts → Evidence a s m v d (.node key dicts)

section
variable {a : Source} {s : Current} {m : Assignment} {v : Views}

mutual
theorem node_sound (checked : SourceChecked s) (cover : Coverage s.environment) (fit : ModelsCurrent s m v)
    (asked : Declared (authoredRegistry s) d) (tree : Tree) (dict : Dictionary)
    (resolves : Resolves (Rule a s) d tree) (summarizes : Summarizes tree (.selected dict)) :
    Evidence a s m v d dict := by
  cases resolves with
  | pending _ => cases summarizes
  | ambiguous _ => cases summarizes
  | rejected _ => cases summarizes
  | selected choice children =>
    obtain ⟨localProof,requests⟩ := local_sound checked cover choice asked m v fit
    cases summarizes with
    | selected results combined =>
      cases combined with
      | selected matching =>
        subst_vars
        exact .node localProof (list_sound checked cover fit requests _ _ children results)
termination_by sizeOf tree

theorem list_sound (checked : SourceChecked s) (cover : Coverage s.environment) (fit : ModelsCurrent s m v)
    (asked : ∀ d ∈ ds,Declared (authoredRegistry s) d) (trees : List Tree) (dicts : List Dictionary)
    (resolves : All₂ (Resolves (Rule a s)) ds trees)
    (summarizes : All₂ Summarizes trees (dicts.map Result.selected)) :
    All₂ (Evidence a s m v) ds dicts := by
  cases dicts with
  | nil => cases summarizes; cases resolves; exact .nil
  | cons first rest =>
    cases summarizes with
    | cons won later =>
      cases resolves with
      | cons has next =>
        exact .cons (node_sound checked cover fit (asked _ List.mem_cons_self) _ _ has won)
          (list_sound checked cover fit (fun d h => asked d (List.mem_cons_of_mem _ h)) _ _ next later)
termination_by sizeOf trees
end

end

theorem dictionary_sound {a : Source} {s : Current}
    (checked : SourceChecked s) (cover : Coverage s.environment)
    (asked : Declared (authoredRegistry s) d) (selected : Classify (Rule a s) d (.selected dict)) :
    ∀ (m : Assignment) (v : Views), ModelsCurrent s m v → Evidence a s m v d dict := by
  obtain ⟨tree,chart,result⟩ := selected
  exact fun _ _ valid => node_sound checked cover valid asked tree dict chart result

end Yulang.GeneralDeclarativeWitnessProjectionRule358
