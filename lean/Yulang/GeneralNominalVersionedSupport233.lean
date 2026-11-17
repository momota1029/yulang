import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalCenteredHeadMatStepSupport

set_option backward.isDefEq.respectTransparency false

/-! Sound versioned support slices, without changing the operational kernel.
Readback checks exact observations, including captured child identities.
Settlement recurses only through recorded versioned plans and their versioned
children; legacy packet settlement is deliberately not imported. Integration
with the mixed legacy trusted cache, availability and completeness remain open. -/
namespace Yulang.GeneralNominalVersionedSupport233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalSupport (Head readsMany)
open GeneralNominalRecursiveInspection (Test)
variable {roles : Roles.RoleDecls}

inductive Discharged (state : State roles) : Occurrence roles → Prop
  | packet (plan : Plan roles) : plan ∈ state.plans →
      (∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet, Discharged state child) →
      Discharged state plan.packet.site.occurrence
  | alias (first last : GeneralNominalDemandMerging.Site roles) :
      first ∈ state.core.erased.current.sites → last ∈ state.core.erased.current.sites →
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity →
      Discharged state first.occurrence → Discharged state last.occurrence

def PacketSettled (state : State roles) (plan : Plan roles) : Prop :=
  plan ∈ state.plans ∧ ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet,
    Discharged state child

theorem packet_settled_demand (done : PacketSettled state plan) :
    Discharged state plan.packet.site.occurrence := .packet plan done.1 done.2

inductive Fact (roles : Roles.RoleDecls) where
  | input (plan : Plan roles)
  | output (effect : Effect roles)
  | merge (first last : Site roles)

def Fact.Holds (model : Assignment) : Fact roles → Prop
  | .input plan => GeneralNominalVersionedPlans231.Inputs plan model
  | .output effect => GeneralNominalVersionedPlans231.Outputs effect.plan model ∧
      effect.Holds model
  | .merge first last => PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed)

def SliceModels (state : State roles) (facts : List (Fact roles)) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.core.erased.source.state model ∧
    (∀ site ∈ state.core.sourceSites, site.Holds model) ∧ ∀ fact ∈ facts, fact.Holds model

def Readback (state : State roles) (facts : List (Fact roles)) (plan : Plan roles) : Prop :=
  ∀ slot ∈ readsMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration) plan.packet.bounds,
    ∀ test observation, Head plan.packet.context.state (plan.packet.context.state.base.source slot) test observation →
      ∀ model, SliceModels state facts model → observation.Holds model

def ClassReadback (state : State roles) (facts : List (Fact roles)) (effect : Effect roles) : Prop :=
  ∀ site ∈ effect.snapshot.sites,
    GeneralNominalSaturationState.Alias effect.snapshot.erased.current
      effect.plan.input.occurrence.identity site.occurrence.identity →
    SameInputs (SliceModels state facts) effect.plan.input site

inductive Trusted (state : State roles) : List (Fact roles) → Prop
  | source : Trusted state []
  | input (plan : Plan roles) : Trusted state facts → plan ∈ state.plans → Readback state facts plan →
      Trusted state (.input plan :: facts)
  | output (effect : Effect roles) : Trusted state facts → effect ∈ state.effects → effect.plan ∈ state.plans →
      Fact.input effect.plan ∈ facts → ClassReadback state facts effect →
      PacketSettled state effect.plan →
      Trusted state (.output effect :: facts)
  | merge (first last : Site roles) : Trusted state facts →
      first ∈ state.core.sites → last ∈ state.core.sites →
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity →
      (∀ atom ∈ GeneralNominalDemandMerging.outputAtoms first.observed last.observed,
        atom ∈ state.core.erased.current.context.state.ordinary) →
      (∀ model, SliceModels state facts model → first.Holds model ∧ last.Holds model) →
      SameInputs (SliceModels state facts) first last → Trusted state (.merge first last :: facts)

def HeadJustified (state : State roles) (identity : Nat) (test : Test) : Prop :=
  ∃ facts, Trusted state facts ∧ ∃ snapshot observation,
    Head snapshot identity test observation ∧ ∀ model, SliceModels state facts model → observation.Holds model

def ReadyAt (state : State roles) (identity : Nat) : Prop :=
  ∃ test observation, Head state.core.erased.current.context.state identity test observation ∧ HeadJustified state identity test

def DecisionGuard (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  (∀ index, ReadyAt state (root.demand.arguments index).1) ∧
  ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.core.erased.current.context root = some bounds →
      ∀ slot ∈ readsMany state.core.erased.current.context.state
        (GeneralNominalInspection.queries state.core.erased.current.context.state
          state.core.erased.current.context.interpretation declaration) bounds,
        ReadyAt state (state.core.erased.current.context.state.base.source slot)

theorem trusted_models (trusted : Trusted state facts)
    (valid : GeneralNominalVersionedJournal232.Models state model) : SliceModels state facts model := by
  refine ⟨valid.1.2.1,fun site member => valid.1.2.2.2.1 site (state.core.sourceRecorded site member),?_⟩
  induction trusted with
  | source => intro fact member; cases member
  | input plan _ recorded _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact (valid.2.1 plan recorded).2.1
      · exact ih fact member
  | output effect _ recorded planRecorded _ _ _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(valid.2.1 effect.plan planRecorded).2.2,(valid.2.2 effect recorded).1⟩
      · exact ih fact member
  | merge first last _ _ _ _ recorded _ _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun atom member => valid.1.1.2.2 atom (recorded atom member)
      · exact ih fact member

theorem outputs_settled (trusted : Trusted state facts) (present : Fact.output effect ∈ facts) :
    PacketSettled state effect.plan := by
  induction trusted with
  | source => cases present
  | input _ _ _ _ ih | merge _ _ _ _ _ _ _ _ _ ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · exact ih present
  | output added _ _ _ _ _ settled ih =>
      rcases List.mem_cons.mp present with equal | present
      · cases equal; exact settled
      · exact ih present

theorem source_head (head : Head state.core.erased.source.state identity test observation) : HeadJustified state identity test :=
  ⟨[],.source,_,observation,head,fun _ valid =>
    GeneralCanonicalObservations.recorded_sound _ _ valid.1 (GeneralNominalSupport.head_recorded head)⟩

theorem justified_readback (justified : HeadJustified state identity test) :
    ∃ snapshot observation, Head snapshot identity test observation ∧
      ∀ model, GeneralNominalVersionedJournal232.Models state model → observation.Holds model := by
  obtain ⟨facts,trusted,snapshot,observation,head,sound⟩ := justified
  exact ⟨snapshot,observation,head,fun model valid => sound model (trusted_models trusted valid)⟩

theorem terminal_settled (present : plan ∈ state.plans)
    (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) : PacketSettled state plan :=
  ⟨present,by intro child member; rw [terminal] at member; cases member⟩

theorem no_unsettled_output (trusted : Trusted state facts)
    (member : child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet)
    (unfinished : ¬ Discharged state child) : Fact.output effect ∉ facts :=
  fun present => unfinished ((outputs_settled trusted present).2 _ member)

end Yulang.GeneralNominalVersionedSupport233
