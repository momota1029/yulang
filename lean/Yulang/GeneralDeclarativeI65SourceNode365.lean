import Yulang.GeneralDeclarativeI65State365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarativeWitnessDeclaredState357 (Joined pointSpans authoredRegistry joined_values)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessClassifyVariance357 (JoinedLocal JoinedMeaning)
open GeneralDeclarativeAssembly320 (Head head_sound)
open GeneralDeclarativeDemand320 (Bounds HeadMeaning bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataRows291 (interpretation)

inductive ReadsHead (s : State) (capture : Nat → Capture) : Capture → Pattern → Prop where
  | ordinary : Head s.current.ordinary (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) capture arg p →
      ReadsHead s capture arg p
  | declared (read : ModeWindow s arg p) : ReadsHead s capture arg p

inductive HeadEvidence (s : State) (m : Model) (capture : Nat → Capture) : Capture → Pattern → Prop where
  | ordinary : HeadMeaning (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) capture m.assignment arg p →
      HeadEvidence s m capture arg p
  | declared (read : ModeWindow s arg p) : WindowMeaning read m →
      HeadEvidence s m capture arg p

theorem heads_have_one_model {s : State} {capture : Nat → Capture} {args pats}
    (reads : All₂ (ReadsHead s capture) args pats) (m : Model) (fit : Fits s m) :
    All₂ (HeadEvidence s m capture) args pats := by
  induction reads with
  | nil => exact .nil
  | cons first _ after =>
    cases first with
    | ordinary h => exact .cons (.ordinary (head_sound h m.assignment fit.1.1)) after
    | declared w => exact .cons (.declared w (mode_window_sound w m fit)) after

inductive ObservedNode (s : State) (q : Request) (row : Declaration) (body : BodyFacts s q row kids) : Prop where
  | ordered (capture : Nat → Capture) :
      (∀ n ∈ row.inputNames, Bounds s.current.ordinary (capture n)) →
      (∀ n ∈ row.inputNames, ((body.spans.find? fun entry => entry.1 == n).map Prod.snd) = some (capture n)) →
      All₂ (ReadsHead s capture) q.demand.arguments row.head →
      ObservedNode s q row body
  | joined (h : Joined s.current q.demand row) :
      body.spans = pointSpans h.firstBinder h.lastBinder h.actualValue →
      ObservedNode s q row body

inductive ObservedMeaning (s : State) (m : Model) (q : Request) (row : Declaration)
    (body : BodyFacts s q row kids) : Prop where
  | ordered (capture : Nat → Capture) :
      (∀ n ∈ row.inputNames,
        InInterval (m.assignment (capture n).lower).1 (m.assignment (capture n).upper).1
          (m.assignment (capture n).center).1) →
      (∀ n ∈ row.inputNames, ((body.spans.find? fun entry => entry.1 == n).map Prod.snd) = some (capture n)) →
      All₂ (HeadEvidence s m capture) q.demand.arguments row.head →
      ObservedMeaning s m q row body
  | joined (h : Joined s.current q.demand row) :
      body.spans = pointSpans h.firstBinder h.lastBinder h.actualValue →
      (∃ a : GeneralDeclarativeWitnessDeclaredState357.Value, m.authoredValues h.actual = some a ∧
        a.tag = h.tag ∧ a.name = h.name ∧ a.arguments = [.inl (m.assignment h.actualValue).1]) →
      (∀ span ∈ pointSpans h.firstBinder h.lastBinder h.actualValue,
        CommonNominalFullCarrier.Equivalent (m.assignment span.2.center).1
          (.union (m.assignment h.firstValue).1 (m.assignment h.lastValue).1)) →
      ObservedMeaning s m q row body

structure SourceNode (s : State) (q : Request) (row : Declaration) (kids : List Request) where
  available : row ∈ visible s q
  declared : DeclarationCovered s.current.environment row
  signature : row.Signature (authoredRegistry s.current).roles
  actual : BodyFacts s q row kids
  head : ObservedNode s q row actual

structure SourceNodeMeaning {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (n : SourceNode s q row kids) (m : Model) : Prop where
  lexical : row ∈ (authoredRegistry s.current).declarations ∧ row.role = q.demand.role
  declarations : DeclarationCovered s.current.environment row
  observed : ObservedMeaning s m q row n.actual
  sameChildren : kids = children q n.actual.demands
  childRequests : ∀ child ∈ n.actual.demands,
    GeneralDeclarativeOutputSource323.Declared (authoredRegistry s.current) child
  fixedTargets : n.actual.body.finished.fixed.map Equation.left = q.demand.outputs.map GeneralSourceState.Output.target
  allFixed : ∀ eq ∈ n.actual.body.finished.fixed, Holds m.assignment eq

/-- This is the semantic assembly of a source node, not the proof
that it wins a whole visible candidate scan. It quantifies over all
states/models, with the unchanged named state shared by every premise. -/
theorem source_node_sound {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (n : SourceNode s q row kids) (m : Model) (fit : Fits s m) : SourceNodeMeaning n m := by
  obtain ⟨targets,rows⟩ := body_facts_sound n.actual m fit
  refine ⟨(visible_exact ..).mp n.available,n.declared,?_,n.actual.order,
    children_are_actual_requests n.actual n.signature,targets,rows⟩
  cases n.head with
  | ordered capture bounds traced observed =>
    exact .ordered capture (fun n h => bounds_sound (bounds n h) m.assignment fit.1.1) traced
      (heads_have_one_model observed m fit)
  | joined h spans =>
    obtain ⟨native,whole⟩ := joined_values h m.assignment m.authoredValues fit.1
    exact .joined h spans native whole

end Yulang.GeneralDeclarativeI65
