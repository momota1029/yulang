import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralDictionarySharedOutputBinderScope

/-! The source already prevents output-only binders in ordinary where inputs.
That does not prevent *named output requests* from sharing a binder. -/
namespace Yulang.GeneralVersionedOutputFlow310
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedFrame231 (binder capture clauseChild frame)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatEffects (BodyHolds compileBody bodyVariables)
open GeneralDictionaryDefaultEvidence204 (OutputWitness)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDictionaryAssociatedProvenance (Body Supplies)

variable {roles : Roles.RoleDecls}

theorem input_excludes_output (plan : Plan roles) {clause : Clause}
    (member : clause ∈ plan.packet.declaration.requirements) {name : Nat}
    (output : name ∈ plan.packet.declaration.outputNames) :
    name ∉ variablesArgs clause.arguments :=
  plan.packet.checked.outputOnly.2 clause member name output

def namedTarget (plan : Plan roles) (equation : Equation) (name : Nat) : GeneralSourceState.Output :=
  ⟨equation.name,binder plan name⟩

theorem named_request (plan : Plan roles) {clause : Clause} (sig : clause.Signature roles)
    {equation : Equation} (member : equation ∈ clause.outputs) {name : Nat}
    (output : name ∈ plan.packet.declaration.outputNames)
    (rhs : normalize equation.rhs = .var name) :
    namedTarget plan equation name ∈ (clauseChild plan.packet clause sig).demand.outputs := by
  change namedTarget plan equation name ∈ clause.outputs.map _
  apply List.mem_map.mpr
  refine ⟨equation,member,?_⟩
  unfold namedTarget GeneralDeclarationDemands.outputTarget binder
  simp only [rhs,ite_eq_left output]

theorem witness_value (plan : Plan roles) (model : Assignment) (output : GeneralSourceState.Output)
    (proof : OutputWitness plan model output) :
    ∃ body expr, Supplies roles plan.packet.declaration output.name body ∧
      compileBody plan body = some expr ∧
      Equivalent (model output.target).1 (value (bodyVariables plan model body) .actual expr) := by
  obtain ⟨body,origin,⟨expr,translated⟩,held⟩ := proof
  refine ⟨body,expr,origin,translated,?_⟩
  unfold BodyHolds GeneralNominalCenteredHeadMatEffects.bodySchema at held
  rw [translated] at held
  exact held _ (List.mem_singleton_self _)

theorem equivalent_through {target left right : Ty}
    (first : Equivalent target left) (last : Equivalent target right) : Equivalent left right :=
  ⟨subtype_trans first.2 last.1,subtype_trans last.2 first.1⟩

/-- Two recursively certified children may have distinct declarations, output
    names and bodies. A named-output binder nevertheless forces their evaluated
    bodies to agree in the *same* model; no equation supplies an input head. -/
theorem paired_certificates {parent first last : Plan roles} {c d : Clause} {m : Assignment}
    (sigC : c.Signature roles) (sigD : d.Signature roles)
    {eqC eqD : Equation} (memC : eqC ∈ c.outputs) (memD : eqD ∈ d.outputs)
    {name : Nat} (output : name ∈ parent.packet.declaration.outputNames)
    (rhsC : normalize eqC.rhs = .var name) (rhsD : normalize eqD.rhs = .var name)
    (left : GeneralNominalVersionedEvidence231.Certificate registry core m
      (clauseChild parent.packet c sigC) keyC kidsC first)
    (right : GeneralNominalVersionedEvidence231.Certificate registry core m
      (clauseChild parent.packet d sigD) keyD kidsD last) :
    ∃ bodyC exprC bodyD exprD,
      Supplies roles first.packet.declaration eqC.name bodyC ∧ compileBody first bodyC = some exprC ∧
      Supplies roles last.packet.declaration eqD.name bodyD ∧ compileBody last bodyD = some exprD ∧
      Equivalent (value (bodyVariables first m bodyC) .actual exprC)
        (value (bodyVariables last m bodyD) .actual exprD) := by
  obtain ⟨bodyC,exprC,givenC,compC,evalC⟩ := witness_value first m _
    (left.outputs _ (named_request parent sigC memC output rhsC))
  obtain ⟨bodyD,exprD,givenD,compD,evalD⟩ := witness_value last m _
    (right.outputs _ (named_request parent sigD memD output rhsD))
  exact ⟨bodyC,exprC,bodyD,exprD,givenC,compC,givenD,compD,equivalent_through evalC evalD⟩

end Yulang.GeneralVersionedOutputFlow310
