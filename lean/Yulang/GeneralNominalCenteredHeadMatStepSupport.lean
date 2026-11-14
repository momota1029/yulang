import Yulang.GeneralNominalCenteredHeadMatStepJournal

set_option backward.isDefEq.respectTransparency false

/-! Corrected support slices never read legacy output facts. Input promotion
requires readback of its inspected observations; output promotion still waits
for the producing packet's children. Refresh is not a support premise. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatStepJournal (State Effect)
open GeneralNominalSupport (Head readsMany)
open GeneralNominalRecursiveInspection (Test)
variable {roles : Roles.RoleDecls}

inductive Fact (roles : Roles.RoleDecls) where
  | input (plan : Plan roles)
  | output (effect : Effect roles)
  | merge (first last : Site roles)

def Fact.Holds (model : Assignment) : Fact roles → Prop
  | .input plan => GeneralNominalCenteredHeadMatStepPackets.Inputs plan model
  | .output effect => GeneralNominalCenteredHeadMatStepPackets.Outputs effect.plan model ∧
      effect.Holds model
  | .merge first last => PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed)

def Models (state : State roles) (facts : List (Fact roles)) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.core.erased.source.state model ∧
    (∀ site ∈ state.core.sourceSites, site.Holds model) ∧ ∀ fact ∈ facts, fact.Holds model

def Readback (state : State roles) (facts : List (Fact roles)) (plan : Plan roles) : Prop :=
  ∀ slot ∈ readsMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration) plan.packet.bounds,
    ∀ test observation, Head plan.packet.context.state (plan.packet.context.state.base.source slot) test observation →
      ∀ model, Models state facts model → observation.Holds model

def ClassReadback (state : State roles) (facts : List (Fact roles)) (effect : Effect roles) : Prop :=
  ∀ site ∈ effect.snapshot.sites,
    GeneralNominalSaturationState.Alias effect.snapshot.erased.current
      effect.plan.input.occurrence.identity site.occurrence.identity →
    SameInputs (Models state facts) effect.plan.input site

inductive Trusted (state : State roles) : List (Fact roles) → Prop
  | source : Trusted state []
  | input (plan : Plan roles) : Trusted state facts → plan ∈ state.core.plans → Readback state facts plan →
      Trusted state (.input plan :: facts)
  | output (effect : Effect roles) : Trusted state facts → effect ∈ state.effects → effect.plan ∈ state.core.plans →
      Fact.input effect.plan ∈ facts → ClassReadback state facts effect →
      GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet →
      Trusted state (.output effect :: facts)
  | merge (first last : Site roles) : Trusted state facts →
      first ∈ state.core.sites → last ∈ state.core.sites →
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity →
      (∀ atom ∈ GeneralNominalDemandMerging.outputAtoms first.observed last.observed,
        atom ∈ state.core.erased.current.context.state.ordinary) →
      (∀ model, Models state facts model → first.Holds model ∧ last.Holds model) →
      SameInputs (Models state facts) first last → Trusted state (.merge first last :: facts)

def HeadJustified (state : State roles) (identity : Nat) (test : Test) : Prop :=
  ∃ facts, Trusted state facts ∧ ∃ snapshot observation,
    Head snapshot identity test observation ∧ ∀ model, Models state facts model → observation.Holds model

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
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) : Models state facts model := by
  refine ⟨valid.2.1,fun site member => valid.2.2.2.1 site (state.core.sourceRecorded site member),?_⟩
  induction trusted with
  | source => intro fact member; cases member
  | input plan _ recorded _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact (valid.2.2.2.2.1 plan recorded).2.1
      · exact ih fact member
  | output effect _ recorded planRecorded _ _ _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(valid.2.2.2.2.1 effect.plan planRecorded).2.2,(valid.2.2.2.2.2 effect recorded).1⟩
      · exact ih fact member
  | merge first last _ _ _ _ recorded _ _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun atom member => valid.1.2.2 atom (recorded atom member)
      · exact ih fact member

theorem outputs_settled (trusted : Trusted state facts) (present : Fact.output effect ∈ facts) :
    GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet := by
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
      ∀ model, GeneralNominalCenteredHeadMatStepJournal.Models state model → observation.Holds model := by
  obtain ⟨facts,trusted,snapshot,observation,head,sound⟩ := justified
  exact ⟨snapshot,observation,head,fun model valid => sound model (trusted_models trusted valid)⟩

end Yulang.GeneralNominalCenteredHeadMatStepSupport
