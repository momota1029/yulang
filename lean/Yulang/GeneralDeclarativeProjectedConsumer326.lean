import Yulang.GeneralDeclarativeProjectCapture326
import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeAppliedSource325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectedConsumer326
open GeneralDeclarations (Checked Declaration Clause Registry)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeFrameReadback325 (sourceNames placeById)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeSourceEmission322 (demand exact_at)
open GeneralDeclarativeProjectCapture326 (capture identities)
open GeneralDeclarativePairNames326 (Span first second)
open GeneralDeclarativeProducedNames325 (exact_input exact_clause_input)
open GeneralDeclarativeNormalizeAssoc324 (one row_iff)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture)
open GeneralDictionaryAssociatedProvenance (Supplies lookup_exact)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceState (Output)

theorem ordered_child {s : State} (kept : List Nat) (l r : Span)
    (place : Placement) (base : Nat → Capture)
    (checked : Checked reg) (visible : impl ∈ reg.declarations)
    {cl : Clause} {childIndex leftIndex rightIndex : Nat} (clauseAt : impl.requirements[childIndex]? = some cl)
    (leftAt : cl.arguments[leftIndex]? = some leftPat)
    (rightAt : cl.arguments[rightIndex]? = some rightPat)
    (leftBare : normalize leftPat = .var left) (rightBare : normalize rightPat = .var right)
    (different : left ≠ right) :
    ∃ child : Demand,
      (children impl (sourceNames impl place (capture s kept left right l r base)) place)[childIndex]? =
        some child ∧
      child.arguments[leftIndex]? = some (first s kept l r) ∧
      child.arguments[rightIndex]? = some (second s kept l r) := by
  let base' := capture s kept left right l r base
  let names := sourceNames impl place base'
  let child := demand impl cl names (place.compound cl) (place.targets cl)
  have entered := List.mem_of_getElem? clauseAt
  have one := exact_at names (place.compound cl) 0 cl.arguments leftIndex leftAt
  have two := exact_at names (place.compound cl) 0 cl.arguments rightIndex rightAt
  have lArg := exact_clause_input (checked.2 impl visible) (placed := placeById impl place)
    (resolved := base') (fallback := place.compound cl (0+leftIndex)) entered (List.mem_of_getElem? leftAt) leftBare
  have rArg := exact_clause_input (checked.2 impl visible) (placed := placeById impl place)
    (resolved := base') (fallback := place.compound cl (0+rightIndex)) entered (List.mem_of_getElem? rightAt) rightBare
  obtain ⟨lEq,rEq⟩ := identities (s := s) (l := l) (r := r) kept base different
  refine ⟨child,?_,?_,?_⟩
  · simp [children,clauseAt,child,names,base']
  · simpa only [child,demand,names,sourceNames,base',lArg,lEq] using one
  · simpa only [child,demand,names,sourceNames,base',rArg,rEq] using two

/-- A real explicitly supplied variable output uses the *actual*
computed capture name and the original fixed request target. A default
body is positional and is intentionally not covered here. -/
theorem fixed_left_output {s : State} (kept : List Nat) (l r : Span)
    (place : Placement) (base : Nat → Capture) (d : Demand) (out : Output)
    (checked : Checked reg) (visible : impl ∈ reg.declarations)
    (supplied : Supplies reg.roles impl out.name (.explicit eq))
    (sourceVar : normalize eq.rhs = .var left)
    (inHead : left ∈ impl.inputNames) (different : left ≠ right) :
    one reg interp impl d (sourceNames impl place (capture s kept left right l r base)).input out =
      some [⟨out.target,.variable (first s kept l r).center⟩] := by
  have listed := (lookup_exact reg.roles impl (checked.2 impl visible).identified.2.2.1 out.name
    (.explicit eq)).mpr supplied
  have lEq := (identities (s := s) (l := l) (r := r) kept base different).1
  have own := exact_input (checked.2 impl visible) (placed := placeById impl place)
    (resolved := capture s kept left right l r base) inHead
  rw [one,listed]
  change (do
    let form ← translate reg.constructors interp (normalize eq.rhs)
    pure [(⟨out.target,GeneralDeclarativeSubstitution320.logical
      (sourceNames impl place (capture s kept left right l r base)).input .actual form⟩ : Equation)]) = _
  rw [sourceVar]
  change some [(⟨out.target,.variable
    ((sourceNames impl place (capture s kept left right l r base)).input left).center⟩ : Equation)] = _
  rw [sourceNames,own,lEq]

end Yulang.GeneralDeclarativeProjectedConsumer326
