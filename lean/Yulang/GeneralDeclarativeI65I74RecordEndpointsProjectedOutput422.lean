import Yulang.GeneralDeclarativeI65I74RecordEndpointsProjectionNames422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open CommonDeclaredNominalInspection (Kind)
open CommonNominalFullCarrier (Ty Row mask)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Checker408 (Problem)
open ExplicitPick419 (exactlyOneOutput)

def Read.outIndex {p} (r : Read p) : Fin p.root.demand.outputs.length :=
  exactlyOneOutput p r.exactOut

/-- Evidence only for the typed *value side* of the original associated
equation. It reads the exact original compiler-atlas entry. It does
not claim a retained equality or head evidence in the frozen engine. -/
structure ProjectedOutput {p} (r : Read p) where
  sourceBody : lookup (authoredRegistry p.state.core.current).roles r.decl
    p.root.demand.outputs[r.outIndex].name = some (.explicit r.assoc)
  plan : B6MixedRhs401 p.state.core false (normalize (bodyPattern (.explicit r.assoc)))
  originalCompiled : p.state.b6.read p.root r.ordinal r.outIndex (.explicit r.assoc) = some plan

def readProjectedOutput422 {p} (r : Read p) : Option (ProjectedOutput r) := do
  if seen : lookup (authoredRegistry p.state.core.current).roles r.decl
      p.root.demand.outputs[r.outIndex].name = some (.explicit r.assoc) then
    match code : p.state.b6.read p.root r.ordinal r.outIndex (.explicit r.assoc) with
    | none => none
    | some plan => pure ⟨seen,plan,code⟩
  else none

/-- This interpretation is purely model-local. There is no slot name
whose assignment could be substituted for the actual projection. -/
def valueOfProjectionBinder422 {p} (r : Read p) (m : I72.Model) :
    (_ : Kind) → (_ : Nat) → Unit → Option (Ty × Row)
  | .row, _, _ => none
  | .value, n, _ =>
    if n = r.fieldBinder then
      (project r.low.label false [] (m.assignment r.arg.center).1).map (fun v => (v,Common.rowEmpty))
    else if n = r.residualBinder then
      some (mask [r.low.label] (m.assignment r.arg.center).1,Common.rowEmpty)
    else none

def ProjectedOutput.actualRightValue {p} {r : Read p} (o : ProjectedOutput r) (m : I72.Model) :
    Option (List Nat × Nat × Nat × Nat × Ty) :=
  (evaluateMixedRhs401 (valueOfProjectionBinder422 r m) o.plan).map fun value =>
    (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,value)

private theorem evaluate_at_literal_binder422 {s : GeneralDeclarativeI65.State} {syntaxTree : Pattern}
    (plan : B6MixedRhs401 s false syntaxTree) {n : Nat}
    (literally : syntaxTree = .var n) (ρ : (_ : Kind) → (_ : Nat) → Unit → Option (Ty × Row)) :
    evaluateMixedRhs401 ρ plan = (ρ .value n ()).map Prod.fst := by
  cases literally
  cases plan
  rfl

/-- Evaluate the *actual compiled source tree* of this binder at the
original model; the result bears the original occurrence, declaration
position, output position and requested target. This is the desired
equation RHS, not a statement that the target has that value. -/
theorem original_B6_binder_yields_required_projection_and_exact_addresses422 {p} {r : Read p}
    (o : ProjectedOutput r) (m : I72.Model) (a : ProjectedRecordChannels r m) :
    o.actualRightValue m =
      some (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,a.required) := by
  have original : normalize (bodyPattern (.explicit r.assoc)) = .var r.fieldBinder := by
    change normalize r.assoc.rhs = _
    rw [r.assocRhs]
    rfl
  unfold ProjectedOutput.actualRightValue
  rw [evaluate_at_literal_binder422 o.plan original]
  simp [valueOfProjectionBinder422,a.atRequired]

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
