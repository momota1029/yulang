import Yulang.GeneralWhereVersionCompiler317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralWhereVersionCase317
open GeneralWhereVersionCompiler317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralLiveCompoundChildSite316 (signature childSite)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralVersionedEndpointAddress315 (atCell fields)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatSchemas (Equation)

abbrev expr : Expr := .variant 0 (.variable 0)
noncomputable abbrev lower := atCell rootPlan .lower otherChild.id 0 expr
noncomputable abbrev upper := atCell rootPlan .upper otherChild.id 0 expr
noncomputable abbrev site := child rootPlan otherChild signature
noncomputable abbrev occ := site.occurrence
noncomputable abbrev lowerRow : Equation := ⟨lower,.lower,expr⟩
noncomputable abbrev upperRow : Equation := ⟨upper,.upper,expr⟩

theorem addresses_differ : lower ≠ upper := by
  intro h
  have s := fields (p := rootPlan) (q := rootPlan) (a := .lower) (b := .upper)
    (c := otherChild.id) (d := otherChild.id) (i := 0) (j := 0) (e := expr) (f := expr) rfl h
  cases s.2.2.1

theorem descriptor : occ.demand.arguments 0 = (lower,upper) := by
  unfold occ site child emit GeneralDeclarationDemands.emit GeneralDeclarationDemands.childDemand
  unfold allocation args
  rfl

theorem centers_preserved : site.center 0 = GeneralMixedCompoundChildEquality307.mid := by
  rw [child_center]
  change (GeneralNominalVersionedFrame231.childSite
     (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLiveCompoundCurrentRoot316.plan)
     otherChild signature).center 0 = _
  rw [GeneralNominalVersionedTransport231.childSite_eq,GeneralLiveCompoundPostRootHead316.child_site,
    GeneralLiveCompoundChildSite316.center_id]

theorem emission_exact : emissions rootPlan = [emit rootPlan otherChild signature] := by
  unfold emissions GeneralCanonicalChildOrder.canonicalEmit
  change GeneralDeclarationDemands.emitAll root.identity
    (GeneralCanonicalChildOrder.canonicalDeclaration GeneralLiveCompoundRegistry316.declaration) _ _ _ = _
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  unfold GeneralDeclarationDemands.emitAll
  change List.map _ ([⟨otherChild,List.mem_singleton_self _⟩] :
    List {c // c ∈ [otherChild]}) = _
  rfl

theorem ordered_children : children rootPlan = [occ] := by
  unfold children
  rw [emission_exact]
  rfl

theorem rows : (schema rootPlan).equations =
    [⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩,lowerRow,upperRow] := by
  unfold schema
  rw [emission_exact]
  rfl

end Yulang.GeneralWhereVersionCase317
