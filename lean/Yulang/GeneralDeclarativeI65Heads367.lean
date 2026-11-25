import Yulang.GeneralDeclarativeI65I75EndpointHeadPremises423
import Yulang.GeneralDeclarativeI65Deep366
import Yulang.GeneralDeclarativeI65SourceNode365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarativeWitnessDeclaredState357 (Joined pointSpans authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeAssembly320 (Head head_sound)
open GeneralDeclarativeDemand320 (Bounds HeadMeaning)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataRows291 (interpretation)

inductive DeepHead (s : State) (capture : Nat → Capture) : Capture → Pattern → Prop where
  | ordinary : Head s.current.ordinary (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) capture arg p →
      DeepHead s capture arg p
  | declared (read : ModeWindow s arg p) :
      DeepRead s capture false (normalize p) read.lower.endpoint read.upper.endpoint found →
      DeepHead s capture arg p

inductive DeepHeadMeaning (s : State) (m : Model) (capture : Nat → Capture) :
    Capture → Pattern → Prop where
  | ordinary : HeadMeaning (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) capture m.assignment arg p →
      DeepHeadMeaning s m capture arg p
  | declared (read : ModeWindow s arg p) :
      DeepRead s capture false (normalize p) read.lower.endpoint read.upper.endpoint found →
      WindowMeaning read m → (∀ b ∈ found, Binding.Denotes capture m b) →
      DeepHeadMeaning s m capture arg p

theorem deep_heads_sound {s : State} {capture : Nat → Capture} {as ps}
    (read : All₂ (DeepHead s capture) as ps) (m : Model) (fit : Fits s m) :
    All₂ (DeepHeadMeaning s m capture) as ps := by
  induction read with
  | nil => exact .nil
  | cons one _ later =>
    cases one with
    | ordinary h => exact .cons (.ordinary (head_sound h m.assignment fit.1.1)) later
    | declared h deep =>
      exact .cons (.declared h deep (mode_window_sound h m fit)
        (deep_binding_means_same_model deep m fit)) later

theorem shallow_head_projection {s : State} {capture : Nat → Capture} {as ps}
    (read : All₂ (DeepHead s capture) as ps) :
    All₂ (ReadsHead s capture) as ps := by
  induction read with
  | nil => exact .nil
  | cons one _ later =>
    cases one with
    | ordinary h => exact .cons (.ordinary h) later
    | declared h _ => exact .cons (.declared h) later

/-- The historical named-frame judgment stays in its original
ordered/joined lane. Endpoint projection is the other lane of the
same head family; it has no total named record capture. -/
inductive SourceHeadLane where
  | named
  | endpoint

/-- Independent source-side head facts, with no generated body or
selected outcome. The joined case keeps the actual whole-payload rule. -/
inductive SourceHead (s : State) (q : Request) (row : Declaration) :
    (lane : SourceHeadLane := .named) → Type where
  | ordered (capture : Nat → Capture) :
      All₂ (DeepHead s capture) q.demand.arguments row.head → SourceHead s q row
  | joined : Joined s.current q.demand row → SourceHead s q row
  | endpointRecord {arg : Capture} {label fieldBinder residualBinder : Nat} :
      q.demand.arguments = [arg] →
      row.head = [.record label (.var fieldBinder) (.var residualBinder)] →
      fieldBinder ≠ residualBinder →
      EndpointHead423.Inputs s arg label → SourceHead s q row .endpoint

inductive HeadModel (s : State) (m : Model) (q : Request) (row : Declaration) :
    {lane : SourceHeadLane} → SourceHead s q row lane → Prop where
  | ordered {capture h} :
      All₂ (DeepHeadMeaning s m capture) q.demand.arguments row.head →
      HeadModel s m q row (.ordered capture h)
  | joined {h : Joined s.current q.demand row} :
      (∃ a : GeneralDeclarativeWitnessDeclaredState357.Value, m.authoredValues h.actual = some a ∧
        a.tag = h.tag ∧ a.name = h.name ∧ a.arguments = [.inl (m.assignment h.actualValue).1]) →
      (∀ span ∈ pointSpans h.firstBinder h.lastBinder h.actualValue,
        CommonNominalFullCarrier.Equivalent (m.assignment span.2.center).1
          (.union (m.assignment h.firstValue).1 (m.assignment h.lastValue).1)) →
      HeadModel s m q row (.joined h)

  | endpointRecord {arg : Capture} {label fieldBinder residualBinder : Nat}
      {atts : q.demand.arguments = [arg]}
      {literal : row.head = [.record label (.var fieldBinder) (.var residualBinder)]}
      {distinct : fieldBinder ≠ residualBinder}
      {inputFacts : EndpointHead423.Inputs s arg label} :
      EndpointHead423.Meaning inputFacts m →
      HeadModel s m q row (.endpointRecord atts literal distinct inputFacts)

theorem source_head_sound {s : State} {q : Request} {row : Declaration} {lane : SourceHeadLane}
    (source : SourceHead s q row lane) (m : Model) (fit : Fits s m) :
    HeadModel s m q row source := by
  cases source with
  | ordered capture given => exact .ordered (deep_heads_sound given m fit)
  | joined h =>
    obtain ⟨a,b⟩ := GeneralDeclarativeWitnessDeclaredState357.joined_values h m.assignment m.authoredValues fit.1
    exact .joined a b
  | endpointRecord _ _ _ inputFacts =>
    exact .endpointRecord (EndpointHead423.source_endpoints_have_projected_meaning423 inputFacts m fit)

end Yulang.GeneralDeclarativeI65
