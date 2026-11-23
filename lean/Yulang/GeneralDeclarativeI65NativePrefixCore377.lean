import Yulang.GeneralDeclarativeI65State365
import Yulang.GeneralDeclarativeI65EarlyPorts369

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Bounds Argument Endpoint effectiveParameter childContext)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open Core.PresenceGeneration (RowTerm)

structure AuthorizedEndpoint (s : State) (accept : Origin → Prop) (logical : Nat) where
  original : Origin
  actual : original ∈ s.origins
  route : OriginRoute s original logical
  authority : accept original

/-- A constructor head inspection anchored at a single actual bound.
No upper observation, comparison job, fit, capture value, or success
of the candidate is structural data of the lower one-sided case.
A separate source rule still decides when this represented look occurs. -/
structure NativeHeadPrefix (s : State) (q : Request) (candidate : Declaration)
    (accept : Origin → Prop) (side : OriginalSide) where
  visibleRow : candidate ∈ visible s q
  index : Nat
  captured : Capture
  atInput : q.demand.arguments[index]? = some captured
  atBound : AuthorizedEndpoint s accept (side.pick captured.lower captured.upper)
  pattern : Pattern
  atPattern : candidate.head[index]? = some pattern
  key : Nat
  written : List Pattern
  actualPattern : normalize pattern = .app key written
  arguments : List (Argument Nat)
  actualEndpoint : atBound.original.endpoint = .nominal key arguments
  tdecl : Use s.current.environment key written.length
  params : List Parameter
  authoredMode : tdecl.mode = .declared params
  laidOut : s.modes[key]? = some params

/-- A child authorized to be made visible before comparing, using
original source ordinal, authored kind/effective variance, and bound
coordinates. Computed position is not yet a logical-site certificate. -/
structure NativeValuePort {s : State} {q : Request} {candidate : Declaration}
    {accept : Origin → Prop} {side : OriginalSide}
    (first : NativeHeadPrefix s q candidate accept side) (inherited : Bool) where
  index : Nat
  actualPattern : Pattern
  written : first.written[index]? = some actualPattern
  parameter : Parameter
  declared : first.params[index]? = some parameter
  typed : (effectiveParameter inherited parameter).kind = .value
  sourceBounds : Bounds (Endpoint Nat)
  sourceAt : first.arguments[index]? = some (.inl sourceBounds)
  entries : List (EndpointPort (Endpoint Nat))
  exactReads : endpointPorts (effectiveParameter inherited parameter).variance side sourceBounds =
    some entries
  which : EndpointPort (Endpoint Nat)
  present : which ∈ entries

structure NativeRowPort {s : State} {q : Request} {candidate : Declaration}
    {accept : Origin → Prop} {side : OriginalSide}
    (first : NativeHeadPrefix s q candidate accept side) (inherited : Bool) where
  index : Nat
  actualPattern : Pattern
  written : first.written[index]? = some actualPattern
  parameter : Parameter
  declared : first.params[index]? = some parameter
  typed : (effectiveParameter inherited parameter).kind = .row
  sourceBounds : Bounds (RowTerm Nat)
  sourceAt : first.arguments[index]? = some (.inr sourceBounds)
  entries : List (EndpointPort (RowTerm Nat))
  exactReads : endpointPorts (effectiveParameter inherited parameter).variance side sourceBounds =
    some entries
  which : EndpointPort (RowTerm Nat)
  present : which ∈ entries

theorem effective_unused_has_no_value_port {s : State} {q : Request} {d : Declaration}
    {accept : Origin → Prop} {side : OriginalSide} {inherited : Bool}
    {first : NativeHeadPrefix s q d accept side} (p : NativeValuePort first inherited)
    (unused : (effectiveParameter inherited p.parameter).variance = .unused) : False := by
  have h := p.exactReads
  rw [unused] at h
  have discarded : endpointPorts .unused side p.sourceBounds = some [] := by
    cases side <;> cases p.sourceBounds <;> rfl
  rw [discarded] at h
  have visibleOnes := p.present
  rw [← Option.some.inj h] at visibleOnes
  cases visibleOnes

theorem native_value_port_at_literal_job {s : State} {q : Request} {d : Declaration}
    {accept : Origin → Prop} {side : OriginalSide} {inherited : Bool}
    {root : NativeHeadPrefix s q d accept side} (p : NativeValuePort root inherited)
    {lo hi : Bounds (Endpoint Nat)}
    (sameSide : side.pick lo hi = p.sourceBounds)
    {jobs : List (CommonRecursiveNominalIntervals.ContextObligation Nat)}
    (ran : CommonRecursiveNominalIntervals.decomposeContextArgument inherited p.parameter (.inl lo) (.inl hi)
      = some jobs) :
    ∃ a b, jobs[p.which.ordinal]? =
        some (childContext inherited p.parameter,CommonRecursiveNominalIntervals.Obligation.value a b) ∧
      p.which.direction.pick (a,b) = p.which.payload := by
  rw [value_jobs_in_context inherited p.parameter p.typed] at ran
  cases made : comparisonPairs (effectiveParameter inherited p.parameter).variance lo hi with
  | none => simp [made] at ran
  | some pairs =>
    have exactPorts := p.exactReads
    rw [← sameSide] at exactPorts
    have known := (endpoint_port_agrees_with_job made exactPorts p.present).1
    unfold EndpointPort.atJob at known
    cases actual : pairs[p.which.ordinal]? with
    | none => simp [actual] at known
    | some pair =>
      obtain ⟨a,b⟩ := pair
      have literal : jobs = (pairs.map fun (x,y) => CommonRecursiveNominalIntervals.Obligation.value x y).map
          (fun obligation => (childContext inherited p.parameter,obligation)) := by
        exact (Option.some.inj (by simpa [made] using ran)).symm
      have emitted : jobs[p.which.ordinal]? =
          some (childContext inherited p.parameter,CommonRecursiveNominalIntervals.Obligation.value a b) := by
        simp [literal,List.getElem?_map,actual]
      exact ⟨a,b,emitted,by simpa [actual] using known⟩

theorem native_row_port_at_literal_job {s : State} {q : Request} {d : Declaration}
    {accept : Origin → Prop} {side : OriginalSide} {inherited : Bool}
    {root : NativeHeadPrefix s q d accept side} (p : NativeRowPort root inherited)
    {lo hi : Bounds (RowTerm Nat)}
    (sameSide : side.pick lo hi = p.sourceBounds)
    {jobs : List (CommonRecursiveNominalIntervals.ContextObligation Nat)}
    (ran : CommonRecursiveNominalIntervals.decomposeContextArgument inherited p.parameter (.inr lo) (.inr hi)
      = some jobs) :
    ∃ a b, jobs[p.which.ordinal]? =
        some (childContext inherited p.parameter,CommonRecursiveNominalIntervals.Obligation.row a b) ∧
      p.which.direction.pick (a,b) = p.which.payload := by
  rw [row_jobs_in_context inherited p.parameter p.typed] at ran
  cases made : comparisonPairs (effectiveParameter inherited p.parameter).variance lo hi with
  | none => simp [made] at ran
  | some pairs =>
    have exactPorts := p.exactReads
    rw [← sameSide] at exactPorts
    have known := (endpoint_port_agrees_with_job made exactPorts p.present).1
    unfold EndpointPort.atJob at known
    cases actual : pairs[p.which.ordinal]? with
    | none => simp [actual] at known
    | some pair =>
      obtain ⟨a,b⟩ := pair
      have literal : jobs = (pairs.map fun (x,y) => CommonRecursiveNominalIntervals.Obligation.row x y).map
          (fun obligation => (childContext inherited p.parameter,obligation)) := by
        exact (Option.some.inj (by simpa [made] using ran)).symm
      have emitted : jobs[p.which.ordinal]? =
          some (childContext inherited p.parameter,CommonRecursiveNominalIntervals.Obligation.row a b) := by
        simp [literal,List.getElem?_map,actual]
      exact ⟨a,b,emitted,by simpa [actual] using known⟩

end Yulang.GeneralDeclarativeI65
