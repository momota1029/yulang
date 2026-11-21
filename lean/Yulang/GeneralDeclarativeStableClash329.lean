import Yulang.GeneralDeclarativeStableModels329
import Yulang.GeneralDeclarativeStableCanonical329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableClash329
open GeneralDeclarativeStableFixture329 (spans base pairRow)
open GeneralDeclarativeOpaqueFixture328 (prepared oldRows leftCapture rightCapture)
open GeneralDeclarativeStableModels329 (assignment before)
open GeneralDeclarativeNestedModels328 (boolType payload int_in_payload payload_gt_int)
open GeneralDeclarativeRepeat320 (int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeStableTies329 (rows pairOf from_use present_entails)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableSelect329 (TieClash)
open GeneralDeclarativeRepeatDecl327 (reg interp arg root impl headCode headPat)
open CommonNominalFullCarrier (Equivalent subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)

abbrev pinInt : Equation := ⟨7,.primitive (.scalar .int) []⟩
abbrev pinBool : Equation := ⟨12,.primitive (.scalar .bool) []⟩
abbrev pinWide : Equation := ⟨8,.join (.variable 3) (.variable 12)⟩
abbrev beforeChoice := appendFacts prepared [pinInt,pinBool,pinWide]
abbrev afterChoice := appendFacts beforeChoice (rows base (spans.map pairOf))

theorem inhabits : Models beforeChoice (assignment int payload) := by
  apply (model_append _).mpr
  refine ⟨before (subtype_refl _) int_in_payload,?_⟩
  intro row present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with x|x|x <;> cases x <;> exact eqv_refl _

theorem from_shape : Heads beforeChoice reg.constructors interp root.arguments impl.head spans := by
  change Heads beforeChoice reg.constructors interp [arg] [headPat] (spans ++ [])
  refine .cons ⟨?_,headCode,pairRow.right,rfl,.row ?_,.primitive (.cons .capture (.cons .capture .nil))⟩ .nil
  · exact ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem impossible : ¬∃ m, Models afterChoice m := by
  rintro ⟨m,fit⟩
  have old := ((model_append m).mp ((model_append m).mp fit).1).2
  have first : Equivalent (m 7).1 int := old pinInt List.mem_cons_self
  have boolean : Equivalent (m 12).1 boolType := old pinBool (List.mem_cons_of_mem _ List.mem_cons_self)
  have wide : Equivalent (m 8).1 (.union (m 3).1 (m 12).1) :=
    old pinWide (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have scalarVisible : GeneralDeclarativeOpaqueFixture328.scalar ∈ oldRows :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have leftInt : Equivalent (m 3).1 int := fit.2 GeneralDeclarativeOpaqueFixture328.scalar (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ scalarVisible)))
  have joined := GeneralNominalCenteredHeadMatPatternSemantics.union_congr leftInt boolean
  have equality : Equivalent (m 8).1 (m 7).1 :=
    from_use (s := afterChoice) (present_entails (fun _ existsHere => List.mem_append_right _ existsHere))
      (show (0,8) ∈ spans.map pairOf from List.mem_cons_of_mem _ List.mem_cons_self) m fit
  exact payload_gt_int ((eqv_trans (eqv_symm (eqv_trans wide joined)) (eqv_trans equality first)).1)

/-- These exact center writes make a previously inhabited ordinary
state contradictory. No detached model choice or failing search is
used to diagnose the tie branch. -/
theorem clash : TieClash beforeChoice reg interp root impl := by
  refine ⟨spans,base,from_shape,?_,⟨_,inhabits⟩,impossible⟩
  intro key named
  have same : key = 0 := by simpa [GeneralDeclarations.Declaration.inputNames,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.variablesArgs,
    GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalize] using named
  subst key
  exact ⟨leftCapture,List.mem_cons_self,rfl⟩

end Yulang.GeneralDeclarativeStableClash329
