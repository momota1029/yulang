import Yulang.GeneralDeclarativeAssembly320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3400000
namespace Yulang.GeneralDeclarativeNamedAgreement320
open GeneralDeclarations (Declaration Registry Equation Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDictionaryAssociatedProvenance (supplies_unique)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralSourceState (Output)

/-- Repeated demands for one associated output in the same declarative
node agree across all actual targets. In particular explicit/default
provenance is unique before comparing their meanings. -/
theorem same_named {r : Registry} {interp : Interpretation} {m : Assignment}
    {d : Demand} {decl : Declaration} {capture : Nat → Capture} {kids : List Demand}
    (checked : Checked r) (node : Meaning r interp m d decl capture kids)
    {first last : Output} (one : first ∈ d.outputs) (two : last ∈ d.outputs)
    (same : first.name = last.name) :
    Equivalent (m first.target).1 (m last.target).1 := by
  obtain ⟨a,firstBody,ea⟩ := node.outputs first one
  obtain ⟨b,lastBody,eb⟩ := node.outputs last two
  have unique := (checked.2 decl node.visible).identified.2.2.1
  rw [← same] at lastBody
  have identical := supplies_unique r.roles decl unique first.name a b firstBody lastBody
  cases identical
  exact eqv_trans ea (eqv_symm eb)

end Yulang.GeneralDeclarativeNamedAgreement320
