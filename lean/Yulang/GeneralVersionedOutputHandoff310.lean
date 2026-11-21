import Yulang.GeneralVersionedOutputFlow310

/-! The current certificates for a parent and an actual named child request
share a semantic type; they do not transfer authority to observe an input head. -/
namespace Yulang.GeneralVersionedOutputHandoff310
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedFrame231 (binder capture clauseChild)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCenteredHeadMatEffects (compileBody bodyVariables)
open GeneralDictionaryDefaultEvidence204 (OutputWitness)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDictionaryAssociatedProvenance (Body Supplies supplies_unique)
open GeneralVersionedOutputFlow310 (named_request witness_value equivalent_through)

variable {roles : Roles.RoleDecls} {m : Assignment}

/-- An explicit parent body referring to an output-only binder relates the
    externally requested target to that binder, under its original provenance. -/
theorem parent_output {parent : Plan roles} {o : GeneralSourceState.Output} {e : Equation} {name : Nat}
    (w : OutputWitness parent m o) (assoc : e ∈ parent.packet.declaration.associated)
    (named : e.name = o.name) (compiled : compileBody parent (.explicit e) = some (.variable name)) :
    Equivalent (m o.target).1 (m (binder parent name)).1 := by
  obtain ⟨body,expr,origin,translated,evaluated⟩ := witness_value parent m o w
  have same := supplies_unique roles parent.packet.declaration parent.packet.checked.identified.2.2.1
    o.name body (.explicit e) origin (.explicit e assoc named)
  subst body
  have equation := Option.some.inj (translated.symm.trans compiled)
  subst expr
  change Equivalent (m o.target).1 (GeneralNominalCenteredHeadMatEffects.variables parent m .actual name) at evaluated
  have actual : GeneralNominalCenteredHeadMatEffects.variables parent m .actual name =
      (m (binder parent name)).1 := by
    rw [← GeneralNominalVersionedPlans231.actual_variables]
    unfold GeneralNominalVersionedPlans231.variables
    change (if name ∈ parent.packet.declaration.outputNames then
      (m (binder parent name)).1 else (m (binder parent name)).1) = _
    split <;> rfl
  rwa [actual] at evaluated

/-- Exact named child output can be composed with the parent's externally
    requested body. Both certificates are at the same state and model. -/
theorem parent_child {parent child : Plan roles} {c : Clause} (sig : c.Signature roles)
    {request assoc : Equation} {o : GeneralSourceState.Output} {name : Nat}
    (within : request ∈ c.outputs) (shared : name ∈ parent.packet.declaration.outputNames)
    (rhs : normalize request.rhs = .var name)
    (rootCert : GeneralNominalVersionedEvidence231.Certificate registry core m root rootKey rootChildren parent)
    (childCert : GeneralNominalVersionedEvidence231.Certificate registry core m (clauseChild parent.packet c sig)
      childKey childChildren child)
    (requested : o ∈ root.demand.outputs) (provided : assoc ∈ parent.packet.declaration.associated)
    (same : assoc.name = o.name) (translated : compileBody parent (.explicit assoc) = some (.variable name)) :
    ∃ body expr, Supplies roles child.packet.declaration request.name body ∧ compileBody child body = some expr ∧
      Equivalent (m o.target).1 (value (bodyVariables child m body) .actual expr) := by
  have first := parent_output (rootCert.outputs o requested) provided same translated
  obtain ⟨body,expr,given,comp,childEq⟩ := witness_value child m _
    (childCert.outputs _ (named_request parent sig within shared rhs))
  exact ⟨body,expr,given,comp,equivalent_through ⟨first.2,first.1⟩ childEq⟩

end Yulang.GeneralVersionedOutputHandoff310
