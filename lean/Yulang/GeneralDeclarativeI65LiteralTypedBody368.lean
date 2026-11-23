import Yulang.GeneralDeclarativeI65Selection367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Row)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeWitnessTypedPacket354 (Accepted Report)
open GeneralDeclarativeWitnessDeclaredState357 (Value observed authoredRegistry emitted_declared)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralSourceMetadataBundle291 (registry)
open GeneralDeclarations (Declaration)

/-- Literal source member used for interpreting a typed fixed row.
This is the source declaration of an already-fixed RHS, not authority
to use an unfinished effective output for a different match. -/
def typedObservation (row : Row) :=
  observed row.root row.tag row.box row.valueName

theorem typed_observation_has_value {s : State} {r : Row}
    (present : typedObservation r ∈ s.current.visible) (m : Model) (fit : Fits s m) :
    ∃ a : Value, m.authoredValues r.root = some a ∧ a.tag = r.tag ∧
      a.name = r.box ∧ a.arguments = [.inl (m.assignment r.valueName).1] := by
  obtain ⟨v,hv,ht,hn,ha⟩ := fit.1.2 _ present
  refine ⟨v,hv,ht,hn,?_⟩
  exact ha

/-- The exact same source declaration, demand, and literal ordered
child list are pinned to the typed body; a matching integer declaration
ID or printed argument alone cannot change its source. -/
structure CurrentTypedBody (s : State) (q : Request) (decl : Declaration)
    (kids : List Request) {p : Problem} {w : Wire} {r : Report}
    (a : Accepted p w s.current.ordinary r) : Prop where
  source : a.output.source.anchor.metadataProof.source = s.current.environment.source
  request : p.demand = q.demand
  row : a.output.source.decl = decl
  ordered : kids = children q a.output.children
  fixed : ∀ x, Write.typed x ∈ r.trace → typedObservation x ∈ s.current.visible

theorem typed_body_ordered_same_model {s : State} {q : Request} {decl : Declaration}
    {kids : List Request} {p : Problem} {w : Wire} {r : Report}
    {a : Accepted p w s.current.ordinary r}
    (body : CurrentTypedBody s q decl kids a) (m : Model) (fit : Fits s m) :
    r.selected = decl.id ∧
    kids = children q a.output.children ∧
    r.kids = a.output.children.map printDemand ∧
    r.trace.map Write.target = q.demand.outputs.map GeneralSourceState.Output.target ∧
    (∀ e ∈ ordinary r.trace, Holds m.assignment e) ∧
    ∀ t, .typed t ∈ r.trace →
      ∃ v : Value, m.authoredValues t.root = some v ∧ v.tag = t.tag ∧
        v.name = t.box ∧ v.arguments = [.inl (m.assignment t.valueName).1] := by
  obtain ⟨targets,equations⟩ :=
    GeneralDeclarativeWitnessTypedPacket354.exact a m.assignment fit.1.1
  have id : r.selected = decl.id := a.selected.trans (congrArg Declaration.id body.row)
  refine ⟨id,body.ordered,a.kids,body.request ▸ targets,equations,?_⟩
  intro t present
  exact typed_observation_has_value (body.fixed t present) m fit

theorem typed_children_have_actual_authoring {s : State} {q : Request} {decl : Declaration}
    {kids : List Request} {p : Problem} {w : Wire} {r : Report}
    {a : Accepted p w s.current.ordinary r}
    (body : CurrentTypedBody s q decl kids a) (pick : AuthoredCandidate s q decl) :
    ∀ request ∈ a.output.children, GeneralDeclarativeOutputSource323.Declared
      (authoredRegistry s.current) request := by
  have same : a.output.source.ctx.registry = authoredRegistry s.current := by
    change registry a.output.source.anchor.metadataProof.source = authoredRegistry s.current
    rw [body.source]
    rfl
  have sig : a.output.source.ctx.decl.Signature a.output.source.ctx.registry.roles := by
    rw [same]
    change a.output.source.decl.Signature (authoredRegistry s.current).roles
    rw [body.row]
    exact pick.signature
  intro request isChild
  have founded := emitted_declared (c := a.output.source.ctx) (ports := a.output.ports) sig isChild
  exact same ▸ founded

/-- Direct declarative typed body cut: the existing typed batch is
run at the independently supplied source context. No C354
`Prepared.only` (single visible declaration) is needed here. This
does not say where the literal typed installations are produced. -/
structure TypedWritten {s : State} {q : Request} {decl : Declaration}
    (ctx : GeneralDeclarativeWitnessCompiler350.Context) (p : Problem)
    (kids : List Request) : Type where
  contextRow : ctx.decl = decl
  currentSource : ctx.registry = authoredRegistry s.current
  currentInterpretation : ctx.interp =
    GeneralSourceMetadataRows291.interpretation s.current.environment.source.snapshot
  nativeSource : GeneralSourceMetadataBareBundle291.compile p.metadata.sourceInput =
    some s.current.environment.source
  contextDemand : ctx.demand = q.demand
  nativeDemand : p.demand = q.demand
  stateAfterPrep : GeneralDeclarativeHead320.State
  ports : List GeneralDeclarativeClauseBatch327.Port
  prep : GeneralDeclarativeWitnessCompiler350.preparation ctx = some (stateAfterPrep,ports)
  whereRows : List GeneralDeclarativeHead320.Equation
  clauses : GeneralDeclarativeWitnessCompiler350.whereBatch ctx ports = some whereRows
  outputs : GeneralDeclarativeWitnessTypedOutput354.Batch p ctx
    (GeneralDeclarativeWitnessCompiler350.portNames ctx ports).input p.demand.outputs
  actualBatch : GeneralDeclarativeWitnessTypedOutput354.batch p ctx
    (GeneralDeclarativeWitnessCompiler350.portNames ctx ports).input p.demand.outputs = some outputs
  ordered : kids = children q (GeneralDeclarativeEmissionForest322.children ctx.decl
    (GeneralDeclarativeWitnessCompiler350.portNames ctx ports)
    (GeneralDeclarativeWitnessCompiler350.placed ctx ports))
  receipt : GeneralDeclarativeCurrentReceipt330.Receipt
    (GeneralDeclarativeEntailment320.appendFacts
      (GeneralDeclarativeEntailment320.appendFacts stateAfterPrep whereRows)
      (ordinary outputs.trace)) s.current.ordinary
  fixedTyped : ∀ x, Write.typed x ∈ outputs.trace → typedObservation x ∈ s.current.visible
  fixedMode : ∀ x, Write.typed x ∈ outputs.trace →
    ∃ use : GeneralDeclarativeWitnessConstructorModes357.Use s.current.environment x.box 1,
      use.mode = .declared [⟨.value,.covariant⟩]

theorem typed_written_all_models {s : State} {q : Request} {decl : Declaration}
    {ctx : GeneralDeclarativeWitnessCompiler350.Context} {p : Problem} {kids : List Request}
    (body : TypedWritten (s := s) (q := q) (decl := decl) ctx p kids)
    (m : Model) (fit : Fits s m) :
    body.outputs.trace.map Write.target = q.demand.outputs.map GeneralSourceState.Output.target ∧
    (∀ e ∈ ordinary body.outputs.trace, Holds m.assignment e) ∧
    ∀ t, .typed t ∈ body.outputs.trace →
      ∃ v : Value, m.authoredValues t.root = some v ∧ v.tag = t.tag ∧
        v.name = t.box ∧ v.arguments = [.inl (m.assignment t.valueName).1] := by
  have kept := GeneralDeclarativeCurrentReceipt330.relays_models body.receipt m.assignment fit.1.1
  have exact := GeneralDeclarativeWitnessTypedOutput354.trace_targets body.outputs
  refine ⟨body.nativeDemand ▸ exact,((GeneralDeclarativeEntailment320.model_append m.assignment).mp kept).2,?_⟩
  intro t present
  exact typed_observation_has_value (body.fixedTyped t present) m fit

end Yulang.GeneralDeclarativeI65
