import Yulang.GeneralDeclarativeI65SourceTree365
import Yulang.GeneralDeclarativeWitnessTypedRelease354

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire)
open GeneralDeclarativeWitnessTypedPacket354 (Accepted Report)
open GeneralDeclarativeWitnessTypedRelease354 (Released Location Authority address exact_ordinal actual_payload)

/-- Retain the exact problem, selected source, requesting occurrence
and row on the common declarative state. This is the same narrow typed
release proved by C354, not a new source rule or another checker. -/
structure TypedFixedRoute (s : State) (q : Request)
    {p : Problem} {w : Wire} {r : Report} {loc : Location} {u : Authority} {i : Nat}
    {a : Accepted p w s.current.ordinary r} (released : Released a loc u i) : Prop where
  sameSource : a.output.source.anchor.metadataProof.source = s.current.environment.source
  sameDemand : p.demand = q.demand
  sameOccurrence : loc.path = q.occurrence

theorem typed_fixed_route_sound {s : State} {q : Request}
    {p : Problem} {w : Wire} {r : Report} {loc : Location} {u : Authority} {i : Nat}
    {a : Accepted p w s.current.ordinary r} {released : Released a loc u i}
    (route : TypedFixedRoute s q released) (m : Model) (fit : Fits s m) :
    a.output.source.anchor.metadataProof.source = s.current.environment.source ∧
    q.demand.outputs[i]? = some released.atWrite.demand ∧
    r.trace[i]? = some (.typed released.atWrite.typed.row) ∧
    released.atWrite.typed.row.root = released.atWrite.demand.target ∧
    (address a loc i released.atWrite.demand).stamp.path = q.occurrence ∧
    CommonNominalFullCarrier.Equivalent (m.assignment released.atWrite.typed.row.valueName).1
      (.union (m.assignment a.output.source.anchor.first.valueName).1
        (m.assignment a.output.source.anchor.last.valueName).1) := by
  have fixed := exact_ordinal released
  exact ⟨route.sameSource,route.sameDemand ▸ fixed.1,fixed.2.1,fixed.2.2.1,route.sameOccurrence,
    actual_payload released m.assignment fit.1.1⟩

end Yulang.GeneralDeclarativeI65
