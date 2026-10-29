import YulangClosure.FormalPermissionSourceTransport
import YulangClosure.OriginalFormalPermissionProjection
import YulangClosure.FormalPermissionDefinitionCallBridge

/-!
R21, annotation policy §§1.1–1.2: permission, inflow and residual are separate.
This is a source-constructor and evidence-inventory model, NOT a runtime model.
Frozen Rust receipt SHA-256: bc22d7eec58ae1a1c430e9892a431e8cbc713aaaf1e566b993a2e9eb1b51acea.
Cargo exited 101 before the test body. No concrete Observation list or native
chain is instantiated below. The two approved sources have independent keys. An invocation *label* supplied
by the candidate probe is not a native invocation identity.

Only the three candidate observations below have inspected emission owners:
lib.rs, r21_annotated_relay_trace::solve_case; permission export is owned by
shadow_apply.rs::formal_effect_permissions. No observed constructor supplies
callback/computation execution arrival, local Catch selection or outer receive.
The missing edges are queries, deliberately not constructors of Observation.
No theorem here assumes a callback-to-Catch bridge.
-/
namespace YulangClosure.FormalPermissionAnnotatedRelay

open FormalPermissionSourceOrigin
open FormalPermissionCaptureConstruction

/-- The already existing negative-concrete port constructor computes the
permission and fresh open row. This does not decode a Rust source occurrence. -/
theorem negative_concrete_port (context : Context) (position signal : Nat) (s : State) :
    constructPort context false (.explicit position [signal] none) s =
      some ⟨sharedPorts s.nextEffect (some (context.metadata position [signal])),
        [⟨context.metadata position [signal], s.nextEffect⟩], [],
        {s with nextEffect := s.nextEffect + 1}⟩ := by
  simp [constructPort]

/-- Apply the retained source-origin result only to an actual successful
constructor and its actual emitted entry, keeping one owner/scope witness. -/
theorem emitted_permission_owner {context : Context} {positive : Bool}
    {source : SourcePort} {before : State} {out : PortResult}
    (built : constructPort context positive source before = some out)
    {entry : FormalPermissionLiveCapture.Emission} (member : entry ∈ out.entries) :
    positive = false ∧ out.ports = sharedPorts entry.row (some entry.metadata) ∧
      entry.row = before.nextEffect ∧ entry.metadata.concrete ≠ [] ∧
      Owned context entry.metadata := port_origin built member

/-- Source tree/path extraction is still required; equal annotation positions
alone do not select a nested callback result effect port. -/
theorem distinct_source_paths (first second : FormalPermissionSourceTransport.SiteKey)
    (different : first.path ≠ second.path) : first ≠ second :=
  FormalPermissionSourceTransport.different_paths_distinct first second different

/-- Candidate observation identity. No actual call/arena identity is claimed
by probeInvocationLabel; owner and occurrence stay on each individual event. -/
structure ProbeKey where
  probe : String
  sourceHash : String
  probeInvocationLabel : String
  deriving DecidableEq, Repr

inductive Kind where
  | permissionProjected | candidateContribution | candidateGraphSolved
  deriving DecidableEq, Repr

structure Observation where
  sequence : Nat
  eventId : String
  key : ProbeKey
  sourceOccurrence : String
  owner : String
  kind : Kind
  deriving DecidableEq, Repr

/-- Restrict to exact source/probe identity and kind, not a family match. -/
def At (events : List Observation) (key : ProbeKey) (kind : Kind)
    (event : Observation) : Prop :=
  event ∈ events ∧ event.key = key ∧ event.kind = kind

/-- The strongest owner-linked prefix supplied by the inspected candidate
inventory. Contribution membership is NOT actual signal inflow to a Catch. -/
def CandidatePrefix (events : List Observation) (key : ProbeKey)
    (permission contribution : Observation) : Prop :=
  At events key .permissionProjected permission ∧
  At events key .candidateContribution contribution ∧
  permission.owner = contribution.owner ∧ permission.sequence < contribution.sequence

theorem prefix_keeps_same_source {events : List Observation} {key : ProbeKey}
    {permission contribution : Observation}
    (prefix : CandidatePrefix events key permission contribution) :
    permission.key = contribution.key ∧ permission.owner = contribution.owner :=
  ⟨prefix.1.2.1.trans prefix.2.1.2.1.symm, prefix.2.2.1⟩

theorem foreign_probe_rejected {events : List Observation} {key : ProbeKey}
    {kind : Kind} {event : Observation} (foreign : event.key ≠ key) :
    ¬ At events key kind event := fun evidence => foreign evidence.2.1

/-- Separate queries for missing constructor/consumer evidence. They are not
native transitions or permission constructors, and have no positive decoder. -/
inductive MissingEdge where
  | contributionToInvocationCatch
  | exactLocalCatchSelection
  | sameWriteToOuterReceive
  deriving DecidableEq, Repr

/-- No inspected candidate observation emits one of these execution edges.
Returning none states the inventory's limit, not absence of native execution. -/
def executionEdge (_event : Observation) : Option MissingEdge := none

def Supplies (events : List Observation) (edge : MissingEdge) : Prop :=
  ∃ event ∈ events, executionEdge event = some edge

theorem candidate_inventory_supplies_no_execution (events : List Observation)
    (edge : MissingEdge) : ¬ Supplies events edge := by
  intro supplied
  obtain ⟨event, _, decoded⟩ := supplied
  cases decoded

/-- The first required edge cannot be recovered by joining permission and
contribution observations, even if those observations have the same owner. -/
theorem prefix_does_not_supply_arrival {events : List Observation} {key : ProbeKey}
    {permission contribution : Observation}
    (_prefix : CandidatePrefix events key permission contribution) :
    ¬ Supplies events .contributionToInvocationCatch :=
  candidate_inventory_supplies_no_execution events .contributionToInvocationCatch

/-- The inspected Apply constructor emits only callee/invocation constraints.
This uses the original theorem without equating constraint and event flow. -/
theorem apply_constraint_target {Value Effect : Type}
    {call : FormalPermissionDefinitionCallBridge.ApplyPorts Value Effect}
    {lower upper : Effect}
    (edge : FormalPermissionDefinitionCallBridge.ApplyEffectEdge call lower upper) :
    upper = call.applicationEffect :=
  FormalPermissionDefinitionCallBridge.effect_edge_target edge

/-!
Parent application: negative_concrete_port and emitted_permission_owner apply
at the annotation constructor only. The inspected source exporters and frozen
receipt must independently decode its context, source position and port.
No receipt label establishes a native invocation or event identity. The first
remaining edge is the supplied callback/computation's exact contribution ->
same actual relay invocation's local Catch (including owner, scope and port).
Exact selection/return 1 and companion write survival to receive follow later.
OriginalEffectHygiene's publication/replay premises and SourceGenerated's typed
execution history are not supplied; their results are not applied to a trace.
All-source A/B, effect hygiene, soundness and production remain OPEN.
-/
end YulangClosure.FormalPermissionAnnotatedRelay
