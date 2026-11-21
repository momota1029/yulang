import Yulang.GeneralDeclarativeNestedModels328
import Yulang.GeneralDeclarativeNestedBatch328
import Yulang.GeneralDeclarativeOpaqueFixtureModels328
import Yulang.GeneralDeclarativeOpaqueAuditGraph328

open Yulang
open CommonNominalFullCarrier (Ty nominal Equivalent)
open GeneralDeclarativeOpaqueDiagnostic328 (old next)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (Models Equation)

section LiteralProjection
def intTy : Ty := .base .int
def boolTy : Ty := .base .bool
def maskPair : Ty := .mask [99] (.inter
  (CommonNominalFullCarrier.pair intTy .top) (CommonNominalFullCarrier.pair .top boolTy))

example : GeneralDeclarativeOpaqueChannel328.project false maskPair = some (.inter intTy .top) := rfl
example : GeneralDeclarativeOpaqueChannel328.project true maskPair = some (.inter .top boolTy) := rfl
example : GeneralDeclarativeOpaqueChannel328.project false (.top : Ty) = none := rfl
example : GeneralDeclarativeOpaqueVariant328.project 3 (CommonNominalFullCarrier.variant 4 intTy) = none := rfl
example : GeneralDeclarativeOpaqueVariant328.project 4
    (.inter (CommonNominalFullCarrier.variant 4 intTy) .top) = some intTy := rfl
end LiteralProjection

section IndependentNames
open GeneralDeclarativeNestedDecl328 (root impl)
open GeneralDeclarativeNestedState328 (initial sourceRows final chosenPlan cooked child rootRow childRow)
open GeneralDeclarativeNestedFrame328 (placement parentBase)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeFrameReadback325 (sourceNames)

example : cooked.binds = [(0,⟨3,17,4⟩),(1,⟨9,9,9⟩)] := rfl
example : children impl (sourceNames impl placement parentBase) placement = [child] := rfl
example : final.equations = sourceRows ++
    ([⟨1,GeneralDeclarativePairCenters326.pair (.variable 15) (.variable 16)⟩,
      ⟨15,.variant 4 (.variable 17)⟩,⟨16,.nominal 0 [.variable 9]⟩,⟨6,.variable 5⟩,⟨5,.variable 17⟩] :
      List Equation) := rfl
example : ¬∃ code, (⟨1,code⟩ : Equation) ∈ initial.equations :=
  GeneralDeclarativeNestedModels328.genuine_nested.1
example : GeneralDeclarativeNestedBatch328.independently_checked = rfl := Subsingleton.elim _ _
example : GeneralDeclarativeOpaqueBatch328.check
    [child,⟨2,[GeneralDeclarativeNestedState328.left],[⟨1,6⟩]⟩]
    [⟨2,[GeneralDeclarativeNestedState328.left],[⟨1,6⟩]⟩,child] = false := rfl
end IndependentNames

example : (∃ m, Models old m) ∧ (∃ m, Models next m) ∧
    (∀ n, ¬AliasCycle old (observed old) n) ∧ AliasCycle next (observed next) 3 :=
  GeneralDeclarativeOpaqueDiagnostic328.separates

#print axioms Yulang.GeneralDeclarativeOpaquePair328.reconstruction
#print axioms Yulang.GeneralDeclarativeOpaqueVariant328.reconstruction
#print axioms Yulang.GeneralDeclarativeOpaqueFixtureModels328.exact_opaque_fixture
#print axioms Yulang.GeneralDeclarativeNestedModels328.genuine_nested
#print axioms Yulang.GeneralDeclarativeOpaqueCompress328.alias_exact
#print axioms Yulang.GeneralDeclarativeOpaqueAuditGraph328.cycle
