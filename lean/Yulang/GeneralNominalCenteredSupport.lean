import Yulang.GeneralNominalCenters

/-! Settled output readback through explicit actual names. Input facts are
justified before outputs; output promotion requires the exact packet to be
settled. No raw optional capture is required by the centered promotion rule. -/
namespace Yulang.GeneralNominalCenteredSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSupport (Tracked Head readsMany)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test)

/-- Input equations exclude the named-output schema. -/
def Inputs (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalPacketSupport.Inputs plan.packet model ∧
  plan.input.Holds model ∧
  (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (plan.binder name)).1) ∧
  plan.SchemaHolds plan.headSchema model ∧
  plan.SchemaHolds (GeneralNominalPacketSupport.inputSchema plan.packet) model ∧
  (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
    (plan.childSite clause valid).Holds model ∧ plan.SchemaHolds (plan.schema (plan.childRequests clause valid)) model)

def Outputs (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalPacketSupport.Outputs plan.packet model ∧
    plan.SchemaHolds (GeneralNominalPacketSupport.namedSchema plan.packet) model

theorem split_packet (valid : plan.Holds model) : Inputs plan model ∧ Outputs plan model := by
  have packet := (GeneralNominalPacketSupport.packet_exact plan.packet model).mp valid.1
  exact ⟨⟨packet.2.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,valid.2.2.2.2.2.2⟩,
    packet.2.2,valid.2.2.2.2.2.1⟩

inductive Fact (roles : Roles.RoleDecls) where
  | input (plan : Plan roles)
  | output (plan : Plan roles)
  | legacy (fact : GeneralNominalSupport.Fact roles)
  | merge (first last : Site roles)

def Fact.Holds (fact : Fact roles) (model : Assignment) : Prop :=
  match fact with
  | .input plan => Inputs plan model
  | .output plan => Outputs plan model
  | .legacy fact => fact.Holds model
  | .merge first last => PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed)

def Models (state : Tracked roles) (roots : List (Site roles)) (facts : List (Fact roles)) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.source.state model ∧
    (∀ site ∈ roots, site.Holds model) ∧ ∀ fact ∈ facts, fact.Holds model

def Readback (state : Tracked roles) (roots : List (Site roles)) (facts : List (Fact roles)) (plan : Plan roles) : Prop :=
  ∀ slot ∈ readsMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration) plan.packet.bounds,
    ∀ test observation, Head plan.packet.context.state (plan.packet.context.state.base.source slot) test observation →
      ∀ model, Models state roots facts model → observation.Holds model

inductive Trusted (state : Tracked roles) (roots : List (Site roles)) (plans : List (Plan roles)) : List (Fact roles) → Prop
  | source : Trusted state roots plans []
  | legacy (facts : List (GeneralNominalSupport.Fact roles)) (readbacks : GeneralNominalSharedSupport.Readbacks) :
      GeneralNominalSharedSupport.Trusted state facts readbacks → Trusted state roots plans (facts.map .legacy)
  | input (plan : Plan roles) (support : List (Occurrence roles)) :
      Trusted state roots plans facts → plan ∈ plans →
      GeneralNominalSupport.Fact.inputs plan.packet support ∈ state.facts → Readback state roots facts plan →
      Trusted state roots plans (.input plan :: facts)
  | output (plan : Plan roles) (support : List (Occurrence roles)) :
      Trusted state roots plans facts → plan ∈ plans →
      GeneralNominalSupport.Fact.outputs plan.packet support ∈ state.facts → Fact.input plan ∈ facts →
      GeneralNominalSettledSupport.PacketSettled state.current plan.packet →
      Trusted state roots plans (.output plan :: facts)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      Trusted state roots plans facts →
      GeneralNominalSupport.Fact.merge first.observed last.observed support ∈ state.facts →
      (∀ model, Models state roots facts model → first.Holds model ∧ last.Holds model) →
      SameInputs (Models state roots facts) first last →
      Trusted state roots plans (.merge first last :: facts)

def HeadJustified (state : Tracked roles) (roots : List (Site roles)) (plans : List (Plan roles))
    (identity : Nat) (test : Test) : Prop :=
  ∃ facts, Trusted state roots plans facts ∧ ∃ snapshot observation,
    Head snapshot identity test observation ∧ ∀ model, Models state roots facts model → observation.Holds model

def ReadyAt (state : Tracked roles) (roots : List (Site roles)) (plans : List (Plan roles)) (identity : Nat) : Prop :=
  ∃ test observation, Head state.current.context.state identity test observation ∧ HeadJustified state roots plans identity test

def DecisionGuard (registry : Registry) (state : Tracked roles) (roots : List (Site roles))
    (plans : List (Plan roles)) (root : Occurrence roles) : Prop :=
  (∀ index, ReadyAt state roots plans (root.demand.arguments index).1) ∧
  ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds →
      ∀ slot ∈ readsMany state.current.context.state
        (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
        ReadyAt state roots plans (state.current.context.state.base.source slot)

theorem legacy_models (valid : Models state roots (facts.map Fact.legacy) model) :
    GeneralNominalSharedSupport.Models state facts model :=
  ⟨valid.1,fun fact member => valid.2.2 (.legacy fact) (List.mem_map.mpr ⟨fact,member,rfl⟩)⟩

theorem legacy_ready (ready : GeneralNominalSharedSupport.ReadyAt state identity) : ReadyAt state roots plans identity := by
  obtain ⟨test,observation,seen,facts,readbacks,trusted,snapshot,witness,recorded,sound⟩ := ready
  exact ⟨test,observation,seen,facts.map Fact.legacy,.legacy facts readbacks trusted,
    snapshot,witness,recorded,fun model valid => sound model (legacy_models valid)⟩

theorem legacy_decision (guard : GeneralNominalSharedSupport.DecisionGuard registry state root) :
    DecisionGuard registry state roots plans root :=
  ⟨fun index => legacy_ready (guard.1 index),fun declaration member role bounds located slot visited =>
    legacy_ready (guard.2 declaration member role bounds located slot visited)⟩

theorem outputs_settled (trusted : Trusted state roots plans facts) (present : Fact.output plan ∈ facts) :
    GeneralNominalSettledSupport.PacketSettled state.current plan.packet := by
  induction trusted with
  | source => cases present
  | legacy facts readbacks old =>
      obtain ⟨fact,_,impossible⟩ := List.mem_map.mp present
      cases impossible
  | input added support previous member recorded readback ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · exact ih present
  | merge first last support previous recorded holds same ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · exact ih present
  | output added support previous member recorded included settled ih =>
      rcases List.mem_cons.mp present with equal | present
      · cases equal; exact settled
      · exact ih present

theorem output_coherent (valid : Outputs plan model) :
    GeneralNominalOriginTerms.Coherent model (GeneralNominalPacketSupport.namedSchema plan.packet)
      (fun name => .leaf (.source (plan.binder name))) := by
  refine ⟨valid.2.1,?_⟩
  intro entry member actual
  have same := valid.2.2 entry member
  simpa only [actual,ite_true,GeneralNominalOriginTerms.Holds] using same

structure OutputCertificate (plan : Plan roles) where
  substitution : Nat → GeneralNominalOriginTerms.Expr GeneralNominalRecursiveInspection.Origin
  coherent : ∀ model, Outputs plan model →
    GeneralNominalOriginTerms.Coherent model (GeneralNominalPacketSupport.namedSchema plan.packet) substitution

def outputCertificate (plan : Plan roles) : OutputCertificate plan :=
  ⟨fun name => .leaf (.source (plan.binder name)),fun _ valid => output_coherent valid⟩

theorem output_certificate_total (plan : Plan roles) : Nonempty (OutputCertificate plan) :=
  ⟨outputCertificate plan⟩

theorem output_readback (valid : Outputs plan model)
    (recipe : GeneralNominalOriginTerms.Recipe (GeneralNominalPacketSupport.namedSchema plan.packet) origin term) :
    GeneralNominalOriginTerms.Holds model (term.bind (fun name => .leaf (.source (plan.binder name)))) origin :=
  GeneralNominalOriginTerms.recipe_readback recipe (output_coherent valid)

/-- Promotion uses the centers already present in the named schema. It does
not reconstruct a raw inherited capture or choose a type inside an interval. -/
theorem settled_output_ready
    (trusted : Trusted state roots plans facts) (planMember : plan ∈ plans)
    (recorded : GeneralNominalSupport.Fact.outputs plan.packet support ∈ state.facts)
    (included : Fact.input plan ∈ facts)
    (settled : GeneralNominalSettledSupport.PacketSettled state.current plan.packet)
    (seen : Head state.current.context.state identity test observation)
    (sound : ∀ model, Models state roots facts model → Outputs plan model → observation.Holds model) :
    ReadyAt state roots plans identity := by
  refine ⟨test,observation,seen,.output plan :: facts,
    .output plan support trusted planMember recorded included settled,_,observation,seen,?_⟩
  intro model valid
  exact sound model ⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (List.mem_cons_of_mem _ member)⟩
    (valid.2.2 _ (List.mem_cons_self ..))

end Yulang.GeneralNominalCenteredSupport
