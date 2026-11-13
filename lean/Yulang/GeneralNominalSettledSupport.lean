import Yulang.GeneralNominalValueBudget

/-! Head explanations after decision 7. Settlement belongs to the exact
output packet. A finite explanation rechecks inherited observations before
using input facts, and may use equal-input facts without settling the two
requests. The ordinary journal and its model set are not filtered. -/
namespace Yulang.GeneralNominalSettledSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test)

abbrev Settled (state : State roles) (demand : Occurrence roles) : Prop := Discharged state demand

def PacketSettled (state : State roles) (packet : Packet roles) : Prop :=
  packet ∈ state.packets ∧ ∀ child ∈ packet.children, Settled state child

def Unsettled (state : State roles) (packet : Packet roles) : Prop :=
  packet ∈ state.packets ∧ ∃ child ∈ packet.children, ¬ Settled state child

theorem packet_settled_demand (done : PacketSettled state packet) : Settled state packet.site.occurrence :=
  .packet packet done.1 done.2

theorem unsettled_iff (present : packet ∈ state.packets) :
    Unsettled state packet ↔ ¬ PacketSettled state packet := by
  classical
  constructor
  · rintro ⟨_,child,member,unfinished⟩ done
    exact unfinished (done.2 child member)
  · intro unfinished
    refine ⟨present,?_⟩
    apply Classical.byContradiction
    intro absent
    apply unfinished
    refine ⟨present,?_⟩
    intro child member
    exact Classical.byContradiction (fun openChild => absent ⟨child,member,openChild⟩)

def Models (state : Tracked roles) (facts : List (Fact roles)) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.source.state model ∧ ∀ fact ∈ facts, fact.Holds model

/-- Exact observations carry the identities of captured children. Equality of
outer tests alone does not license copying those identities into new facts. -/
def Readback (state : Tracked roles) (facts : List (Fact roles)) (packet : Packet roles) : Prop :=
  ∀ slot ∈ readsMany packet.context.state
    (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration) packet.bounds,
    ∀ test observation, Head packet.context.state (packet.context.state.base.source slot) test observation →
      ∀ model, Models state facts model → observation.Holds model

def RecoverySupported (models : Assignment → Prop) (site : GeneralNominalDemandMerging.Site roles) : Prop :=
  ∀ index : Fin (roles site.occurrence.demand.role).arity, site.inputs[index.val]? = some none →
    ∀ model, models model → CommonNominalFullCarrier.Equivalent
      (model (site.occurrence.demand.arguments index).1).1 (model (site.occurrence.demand.arguments index).2).1

def SiteSupported (models : Assignment → Prop) (site : GeneralNominalDemandMerging.Site roles) : Prop :=
  ∀ model, models model → SiteHolds site model

/-- A recovery snapshot is retained in the explanation. Recovery can choose
an endpoint only when equality of the endpoints has an independent explanation. -/
def MergeEvidence (models : Assignment → Prop) (first last : GeneralNominalDemandMerging.Site roles) : Prop :=
  SiteSupported models first ∧ SiteSupported models last ∧
    (GeneralNominalDemandMerging.SameInputs models first last ∨
    ∃ snapshot : State roles,
      GeneralNominalDemandMerging.SameInputs models
        (GeneralNominalFeedbackSites.recover snapshot first) (GeneralNominalFeedbackSites.recover snapshot last) ∧
      RecoverySupported models first ∧ RecoverySupported models last)

inductive Trusted (state : Tracked roles) : List (Fact roles) → Prop
  | source : Trusted state []
  | input (packet : Packet roles) (support : List (Occurrence roles)) :
      Trusted state facts → Fact.inputs packet support ∈ state.facts → Readback state facts packet →
      Trusted state (Fact.inputs packet support :: facts)
  | output (packet : Packet roles) (support : List (Occurrence roles)) :
      Trusted state facts → Fact.outputs packet support ∈ state.facts →
      Fact.inputs packet support ∈ facts → PacketSettled state.current packet →
      Trusted state (Fact.outputs packet support :: facts)
  | merge (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles)) :
      Trusted state facts → Fact.merge first last support ∈ state.facts →
      MergeEvidence (Models state facts) first last →
      Trusted state (Fact.merge first last support :: facts)

def HeadJustified (state : Tracked roles) (identity : Nat) (test : Test) : Prop :=
  ∃ facts, Trusted state facts ∧ ∃ snapshot observation,
    Head snapshot identity test observation ∧ ∀ model, Models state facts model → observation.Holds model

def ReadyAt (state : Tracked roles) (identity : Nat) : Prop :=
  ∃ test observation, Head state.current.context.state identity test observation ∧ HeadJustified state identity test

def DecisionGuard (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  (∀ index, ReadyAt state (root.demand.arguments index).1) ∧
  ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds →
      ∀ slot ∈ readsMany state.current.context.state
        (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
        ReadyAt state (state.current.context.state.base.source slot)

def PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) : Prop :=
  GeneralNominalValueSupport.PacketGuard state packet support ∧
  DecisionGuard packet.registry {state with current := {state.current with context := packet.context}} packet.site.occurrence

theorem trusted_members (trusted : Trusted state facts) : ∀ fact ∈ facts, fact ∈ state.facts := by
  induction trusted with
  | source => simp
  | input _ _ _ member _ ih | output _ _ _ member _ _ ih | merge _ _ _ _ member _ ih =>
    intro fact present
    rcases List.mem_cons.mp present with rfl | present
    · exact member
    · exact ih fact present

theorem trusted_outputs_settled (trusted : Trusted state facts)
    (member : Fact.outputs packet support ∈ facts) : PacketSettled state.current packet := by
  induction trusted with
  | source => cases member
  | input _ _ _ _ _ ih | merge _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp member with impossible | member
    · cases impossible
    · exact ih member
  | output added dependencies _ _ _ done ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same; exact done
    · exact ih member

theorem no_unsettled_output (trusted : Trusted state facts) (openPacket : Unsettled state.current packet) :
    Fact.outputs packet support ∉ facts := by
  intro member
  obtain ⟨child,present,openChild⟩ := openPacket.2
  exact openChild ((trusted_outputs_settled trusted member).2 child present)

theorem all_models (trusted : Trusted state facts) (model : Assignment)
    (valid : AllModels state model) : Models state facts model :=
  ⟨valid.1,fun fact member => valid.2 fact (trusted_members trusted fact member)⟩

theorem head_sound (justified : HeadJustified state identity test) (model : Assignment)
    (valid : AllModels state model) :
    ∃ snapshot observation, Head snapshot identity test observation ∧ observation.Holds model := by
  obtain ⟨facts,trusted,snapshot,observation,head,entailed⟩ := justified
  exact ⟨snapshot,observation,head,entailed model (all_models trusted model valid)⟩

theorem source_head (state : Tracked roles) (head : Head state.source.state identity test observation) :
    HeadJustified state identity test :=
  ⟨[],.source,state.source.state,observation,head,fun model valid =>
    GeneralCanonicalObservations.recorded_sound _ model valid.1 (head_recorded head)⟩

/-- A pending merge can transmit a source-supported output constraint. There
is no settlement premise on the two merge participants. -/
theorem pending_merge_usable (trusted : Trusted state facts)
    (member : Fact.merge first last support ∈ state.facts)
    (firstSite : SiteSupported (Models state facts) first) (lastSite : SiteSupported (Models state facts) last)
    (same : GeneralNominalDemandMerging.SameInputs (Models state facts) first last) :
    Trusted state (Fact.merge first last support :: facts) :=
  .merge first last support trusted member ⟨firstSite,lastSite,Or.inl same⟩

theorem pending_recovered_merge_usable {roles : Roles.RoleDecls} {state : Tracked roles}
    {facts : List (Fact roles)} {first last : GeneralNominalDemandMerging.Site roles}
    {support : List (Occurrence roles)} (trusted : Trusted state facts)
    (member : Fact.merge first last support ∈ state.facts) (snapshot : State roles)
    (firstSite : SiteSupported (Models state facts) first) (lastSite : SiteSupported (Models state facts) last)
    (same : GeneralNominalDemandMerging.SameInputs (Models state facts)
      (GeneralNominalFeedbackSites.recover snapshot first) (GeneralNominalFeedbackSites.recover snapshot last))
    (one : RecoverySupported (Models state facts) first) (two : RecoverySupported (Models state facts) last) :
    Trusted state (Fact.merge first last support :: facts) :=
  .merge first last support trusted member ⟨firstSite,lastSite,Or.inr ⟨snapshot,same,one,two⟩⟩

theorem trusted_monotone {before after : Tracked roles}
    (source : after.source = before.source)
    (facts : ∀ fact ∈ before.facts, fact ∈ after.facts)
    (settlement : ∀ packet, PacketSettled before.current packet → PacketSettled after.current packet)
    (trusted : Trusted before ledger) : Trusted after ledger := by
  have models (entries : List (Fact roles)) : Models after entries = Models before entries := by
    funext model
    simp only [Models,source]
  induction trusted with
  | source => exact .source
  | input packet support _ member readback ih =>
    apply Trusted.input packet support ih (facts _ member)
    intro slot seen test observation head model valid
    exact readback slot seen test observation head model ((congrFun (models _) model) ▸ valid)
  | output packet support _ member included done ih =>
    exact .output packet support ih (facts _ member) included (settlement packet done)
  | merge first last support _ member same ih =>
    apply Trusted.merge first last support ih (facts _ member)
    rw [models]
    exact same

theorem head_monotone {before after : Tracked roles}
    (source : after.source = before.source)
    (facts : ∀ fact ∈ before.facts, fact ∈ after.facts)
    (settlement : ∀ packet, PacketSettled before.current packet → PacketSettled after.current packet)
    (known : HeadJustified before identity test) : HeadJustified after identity test := by
  obtain ⟨ledger,trusted,snapshot,observation,head,entailed⟩ := known
  refine ⟨ledger,trusted_monotone source facts settlement trusted,snapshot,observation,head,?_⟩
  intro model valid
  apply entailed model
  simpa only [Models,source] using valid

end Yulang.GeneralNominalSettledSupport
