import Yulang.GeneralDeclarativeI65I75EndpointHeadPremises423
import Yulang.GeneralDeclarativeI65B6MixedLexical401

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65
namespace ProjectedCore425
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open CommonNominalFullCarrier (Ty Row mask)
open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarativeRecordChannel330 (project)

/-- A low-level typed projection source. Crucially, this module imports
neither I72.Event nor any checker or high-layer receipt; it can be used
under a future canonical event without creating a dependency cycle.
This original B6 source is not a local election judgment. -/
structure Output (s : State) (atlas : B6OccurrenceAtlas401 s) (q : Request)
    (i : Fin q.demand.outputs.length) where
  arg : Capture
  request : q.demand.arguments = [arg]
  label : Nat
  head : EndpointHead423.Inputs s arg label
  fieldBinder : Nat
  tailBinder : Nat
  distinct : fieldBinder ≠ tailBinder
  row : GeneralDeclarations.Declaration
  visibleRow : visible s q = [row]
  ordinal : Nat
  authored : (authoredRegistry s.current).declarations[ordinal]? = some row
  pattern : row.head = [.record label (.var fieldBinder) (.var tailBinder)]
  assoc : GeneralDeclarations.Equation
  originalBody : lookup (authoredRegistry s.current).roles row q.demand.outputs[i].name =
    some (.explicit assoc)
  literalUse : assoc.rhs = .var fieldBinder
  plan : B6MixedRhs401 s false (normalize (bodyPattern (.explicit assoc)))
  atAtlas : atlas.read q ordinal i (.explicit assoc) = some plan

/-- Source models interpret the two binders without allocating named
capture slots. The unneeded typed row branch does not invent a binder. -/
def Output.binderRead {s atlas q i} (o : Output s atlas q i) (m : Model) :
    Kind → Nat → Unit → Option (Ty × Row)
  | .row, _, _ => none
  | .value, n, _ =>
    if n = o.fieldBinder then
      (project o.label false [] (m.assignment o.arg.center).1).map (fun ty => (ty,Common.rowEmpty))
    else if n = o.tailBinder then
      some (mask [o.label] (m.assignment o.arg.center).1,Common.rowEmpty)
    else none

def Output.valueAt {s atlas q i} (o : Output s atlas q i) (m : Model) :
    Option (List Nat × Nat × Nat × Nat × Ty) :=
  (evaluateMixedRhs401 (o.binderRead m) o.plan).map fun v =>
    (q.occurrence,o.ordinal,i.val,q.demand.outputs[i].target,v)

private theorem evaluate_literal425 {s : State} {p : GeneralDeclarationPatterns.Pattern}
    (original : B6MixedRhs401 s false p) {binder : Nat} (eq : p = .var binder)
    (lookup : Kind → Nat → Unit → Option (Ty × Row)) :
    evaluateMixedRhs401 lookup original = (lookup .value binder ()).map Prod.fst := by
  cases eq
  cases original
  rfl

/-- The lower-level event candidate consumes the original retained
B6 source, not the later report evaluator. Separate from target
retention (a local rule must supply the actual ordinary relation). -/
theorem projected_core_original_B6_uses_actual_required_field425
    {s atlas q i} (o : Output s atlas q i) (m : Model) (fit : Fits s m) :
    EndpointHead423.Meaning o.head m ∧
    ∃ v : Ty, project o.label false [] (m.assignment o.arg.center).1 = some v ∧
      o.valueAt m = some (q.occurrence,o.ordinal,i.val,q.demand.outputs[i].target,v) := by
  have meaning := EndpointHead423.source_endpoints_have_projected_meaning423 o.head m fit
  obtain ⟨v,seen,_⟩ := meaning.required
  have syntaxEq : normalize (bodyPattern (.explicit o.assoc)) = .var o.fieldBinder := by
    change normalize o.assoc.rhs = _
    rw [o.literalUse]
    rfl
  refine ⟨meaning,v,seen,?_⟩
  unfold Output.valueAt
  rw [evaluate_literal425 o.plan syntaxEq]
  simp [Output.binderRead,seen]

end ProjectedCore425
end Yulang.GeneralDeclarativeI65
