import Init

/-!
Constructed but UNCHECKED source-constructor schema, not a native instance.
EFFECT-PERMISSION-DEFINITION-CALL-BRIDGE/r1; source baseline bc2a0836ec.

Pinned owners:
* candidate_source.rs:1785-1787: ModuleDef -> PendingDefinitionUse + Module.
* candidate_source.rs:2490-2495: Module -> open-use or incoming route.
* candidate_scheme.rs:4184-4191: validated internal Definition use -> route_internal.
* lib.rs:19179-19187: incoming candidate use -> route_candidate_graph.
* shadow_apply.rs:4105-4176: callee+ <= negative_function(argument+,
  argumentEffect+, invocationEffect-, result-); exact NativeInterface saved.
* shadow_apply.rs:4227-4245: calleeEffect+ <= applicationEffect- and
  invocationEffect+ <= applicationEffect-. These are the ONLY edges below.

Value/Effect parameters stand for row identities after authentic extraction.
They are separate types; positive/negative directions are stated by the edge
relation's positions. This schema does not identify Value and Effect rows,
callee and argument, argument and result, or fresh call and provider rows.
It does not formalize constrain_live_value/effect or certify their propagation.
-/
namespace YulangClosure.FormalPermissionDefinitionCallBridge

/-- Retained Apply ports, not a typing derivation or a returned-provider law.
The invocation row is fresh in graph-effect admission; the Rust constructor
uses its positive and negative terms at the two indicated interfaces. -/
structure ApplyPorts (Value Effect : Type) where
  callee : Value
  argument : Value
  result : Value
  calleeEffect : Effect
  argumentEffect : Effect
  invocationEffect : Effect
  applicationEffect : Effect

/-- Projection of the two actual Effect constraint emissions from one fixed
Apply recipe. An edge records constraint direction, not contribution transport.
Argument evaluation effect enters the Function argument interface, not this
list of direct application joins (shadow_apply.rs:4122-4141,4227-4245). -/
inductive ApplyEffectEdge {Value Effect : Type} (call : ApplyPorts Value Effect) :
    Effect → Effect → Prop where
  | callee : ApplyEffectEdge call call.calleeEffect call.applicationEffect
  | invocation : ApplyEffectEdge call call.invocationEffect call.applicationEffect

/-- A fixed recipe does not emit either direct join at a different target. -/
theorem effect_edge_target {Value Effect : Type} {call : ApplyPorts Value Effect}
    {lower upper : Effect} (edge : ApplyEffectEdge call lower upper) :
    upper = call.applicationEffect := by
  cases edge <;> rfl

/-- The two emissions retain their original lower ports. This is not an
exhaustiveness theorem about the solver's eventual Effect graph. -/
theorem effect_edge_source {Value Effect : Type} {call : ApplyPorts Value Effect}
    {lower upper : Effect} (edge : ApplyEffectEdge call lower upper) :
    lower = call.calleeEffect ∨ lower = call.invocationEffect := by
  cases edge with
  | callee => exact Or.inl rfl
  | invocation => exact Or.inr rfl

/-- Fixed-recipe target substitution falsifier. No contribution, provider or
result identity is inferred from this local constraint-generation statement. -/
theorem substituted_target_rejected {Value Effect : Type}
    {call : ApplyPorts Value Effect} {lower foreign : Effect}
    (different : foreign ≠ call.applicationEffect) :
    ¬ ApplyEffectEdge call lower foreign := by
  intro edge
  exact different (effect_edge_target edge)

/-- candidate_effect.rs:1394-1416 allocates all three fields. An effect family
alone cannot identify an occurrence/contribution. No concrete key is supplied. -/
structure ContributionIdentity (EffectId SourceNode : Type) where
  effect : EffectId
  origin : SourceNode
  allocationInstance : Nat

/-- A partial readout of the exact Contribution operand variant. Owner/node
and full key must be extracted from the same graph snapshot; this record does
not establish authenticity. Support/Permission/Annotation/OperationInterface
variants are not interpreted as contributions by this partial readout. -/
structure ContributionEntry (EffectId SourceNode Graph Node : Type) where
  graph : Graph
  node : Node
  identity : ContributionIdentity EffectId SourceNode

/-- OPEN extraction obligation for a fixed full contribution key, graph owner
and returned-computation row. `entries` must be an authentic Contribution
variant census; `effectBound` must be the authentic Effect lower/upper relation.
Neither premise is supplied here. This definition establishes no instance and
is not a completeness claim for other exported operand representations. -/
def SameContributionExtraction {EffectId SourceNode Graph Node Row : Type}
    (entries : List (ContributionEntry EffectId SourceNode Graph Node))
    (effectBound : Graph → Node → Row → Prop)
    (identity : ContributionIdentity EffectId SourceNode)
    (returnedGraph : Graph) (computation : Row) : Prop :=
  ∃ entry, entry ∈ entries ∧ entry.graph = returnedGraph ∧
    entry.identity = identity ∧ effectBound returnedGraph entry.node computation

/-!
Exact fixture application remains OPEN. Source tuple formation gives a positive
Tuple from actual argument endpoints. TuplePattern admits scrutinee+ against a
negative Tuple built from actual bound components; it emits no direct Effect
constraint (candidate_source.rs:1459-1488; shadow_apply.rs:4044-4054,4081-4104,4261).
The scrutinee is f's CALL RESULT, not its argument. No constructor inspected
identifies those endpoints or transports the callback contribution between them.

First unsupported premise: for the exact module-recursive f pair = f pair,
authenticate the module Definition use and complete Call/provider derivation
connecting the supplied callback's exact contribution to the result component
bound as left, then to the invocation at left 0. Module internal/external routing
is identified above but no source typing theorem for it is instantiated. The
unread candidate_call boundary requires a primary source-scope amendment.

Consequently none of the three local schema theorems is applied as a no-loss
lemma to the fixture. SameContributionExtraction has no concrete instance. The
original all-source A/B claim (2026-10-13 §§1,3,5), H, source/native, principality,
termination and production remain OPEN. No Catch, handler or subtraction claim.
No theorem type or axiom audit has been printed; no Lean/Lake run occurred.
-/
end YulangClosure.FormalPermissionDefinitionCallBridge
