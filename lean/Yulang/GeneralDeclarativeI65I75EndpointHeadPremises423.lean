import Yulang.GeneralDeclarativeI65State365
import Yulang.GeneralDeclarativeEndpointRecord336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
namespace EndpointHead423
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open CommonNominalFullCarrier (Ty record mask subtype_trans)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (sandwich)
open GeneralDeclarativeEndpointRecord336 (mask_below)

/-- An original record endpoint observed in two independent source carriers:
the authored syntax attached to its slot and the exact retained ordinary row.
It contains no read, equation, or new logical name at the requested center. -/
structure Original (s : State) (slot label : Nat) where
  field : Nat
  residual : Nat
  origin : Origin
  attached : origin ∈ s.origins
  correctSlot : origin.slot = slot
  correctSyntax : origin.endpoint =
    .ordinary (.record label (.var field) (.var residual))
  equation : (⟨slot,.record label (.variable field) (.variable residual)⟩ : Equation)
    ∈ s.current.ordinary.equations

/-- Independent source inputs used by an endpoint head, at the actual
demanded interval. Its premises do not mention a model or selected outcome. -/
structure Inputs (s : State) (arg : Capture) (label : Nat) where
  lower : Original s arg.lower label
  upper : Original s arg.upper label
  bounds : Bounds s.current.ordinary arg

def value {s slot label} (o : Original s slot label) (m : Model) : Ty :=
  record label (m.assignment o.field).1 (m.assignment o.residual).1

/-- The field captured in either observation and the retained context of
the original center, not a literal reconstructed record or new slot. -/
structure Meaning {s arg label} (h : Inputs s arg label) (m : Model) : Prop where
  required : ∃ a, project label false [] (m.assignment arg.center).1 = some a ∧
    InInterval (m.assignment h.lower.field).1 (m.assignment h.upper.field).1 a
  optional : ∃ a, project label true [] (m.assignment arg.center).1 = some a ∧
    InInterval (m.assignment h.lower.field).1 (m.assignment h.upper.field).1 a
  residual : InInterval (mask [label] (value h.lower m)) (mask [label] (value h.upper m))
    (mask [label] (m.assignment arg.center).1)

/-- General same-model endpoint soundness at the earliest acyclic
dependency layer: neither checker, R14, event compilation nor B6 is assumed. -/
theorem source_endpoints_have_projected_meaning423 {s arg label}
    (h : Inputs s arg label) (m : Model) (fit : Fits s m) : Meaning h m := by
  have lo : CommonNominalFullCarrier.Equivalent (m.assignment arg.lower).1 (value h.lower m) :=
    fit.1.1.2 _ h.lower.equation
  have hi : CommonNominalFullCarrier.Equivalent (m.assignment arg.upper).1 (value h.upper m) :=
    fit.1.1.2 _ h.upper.equation
  have bound := bounds_sound h.bounds m.assignment fit.1.1
  have low := subtype_trans lo.2 bound.1
  have high := subtype_trans bound.2 hi.1
  exact ⟨sandwich label false low high,sandwich label true low high,
      mask_below _ low,mask_below _ high⟩

end EndpointHead423
end Yulang.GeneralDeclarativeI65
