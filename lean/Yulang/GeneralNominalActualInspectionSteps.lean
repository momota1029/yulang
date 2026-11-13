import Yulang.GeneralNominalSharedSteps

/-! K2 certificates for actual inspected origins. Recovery uses established
input identity, and missing position certificates leave expansion pending. -/
namespace Yulang.GeneralNominalActualInspectionSteps
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalSupport GeneralNominalDemandMerging

def Represents (state : State roles) (origin : Origin) (identity : Nat) : Prop :=
  SameOrigin (Models state) origin (.source identity)

theorem point_argument_readback (state : State roles)
    (parent leaf : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (found : descriptor.arguments[index]? = some (.type (leaf,leaf))) :
    Represents state (.nominal (.source (state.context.state.base.source parent)) descriptor.declaration.name index)
      (state.context.state.base.source leaf) := by
  intro model valid
  obtain ⟨observed,all⟩ := nominal_argument_bounds state.context.state model valid.1 parent descriptor recorded index (leaf,leaf) found
  refine ⟨observed,⟨_,.source _⟩,?_⟩
  intro a b seen source
  cases source
  exact ⟨(all a seen).2,(all a seen).1⟩

theorem nominal_alias_readback (state : State roles)
    (alias : GeneralNominalFeedbackK2.Equal state first last)
    (readback : Represents state (.nominal (.source last) name index) identity) :
    Represents state (.nominal (.source first) name index) identity := by
  intro model valid
  have same := alias model valid
  have transfer : ∀ value, Observes model (.nominal (.source first) name index) value ↔
      Observes model (.nominal (.source last) name index) value := by
    intro value
    constructor
    · intro seen
      cases seen with
      | nominal parent equal found =>
        cases parent
        exact .nominal (.source last)
          ⟨CommonNominalFullCarrier.subtype_trans same.2 equal.1,
            CommonNominalFullCarrier.subtype_trans equal.2 same.1⟩ found
    · intro seen
      cases seen with
      | nominal parent equal found =>
        cases parent
        exact .nominal (.source first)
          ⟨CommonNominalFullCarrier.subtype_trans same.1 equal.1,
            CommonNominalFullCarrier.subtype_trans equal.2 same.2⟩ found
  obtain ⟨⟨value,seen⟩,other,all⟩ := readback model valid
  exact ⟨⟨value,(transfer value).mpr seen⟩,other,fun a b one two => all a b ((transfer a).mp one) two⟩

def Located (state : State roles) (origin : Origin) : Prop :=
  ∃ identity ∈ GeneralNominalState.sources state.context.state, Represents state origin identity

def Cyclic (state : State roles) (origin : Origin) : Prop :=
  ∃ identity, Represents state origin identity ∧ GeneralNominalFeedbackK2.RecursAt state identity

noncomputable def inspection (state : State roles) (packet : Packet roles) : Report packet.context.state :=
  inspectMany packet.context.state
    (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)
    packet.bounds (fun index => ((GeneralNominalFeedbackSites.recover state packet.site).inputs[index]?).join) 0

/-- Each visited constructor position needs its actual origin, a represented
source identity, and exclusion of cycles at every equivalent representative. -/
def Safe (state : State roles) (packet : Packet roles) : Prop :=
  (inspection state packet).inspected.length = (inspection state packet).tests.length ∧
    ∀ entry ∈ (inspection state packet).tests, Located state entry.1 ∧ ¬ Cyclic state entry.1

def AlternativesSafe (registry : Registry) (state : State roles) (site : Site roles) : Prop :=
  ∀ declaration ∈ registry.declarations,
    ∀ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = site.occurrence.demand.role →
      GeneralNominalRecursiveCandidates.HeadReady registry state.context site.occurrence declaration →
      ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.context site.occurrence = some bounds →
        Safe state ⟨registry,state.context,site,declaration,checked,bounds⟩

def PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) : Prop :=
  GeneralNominalSharedSteps.PacketGuard state packet support ∧ Safe state.current packet ∧
    AlternativesSafe packet.registry state.current packet.site

inductive At (registry : Registry) (before : Tracked roles) : Occurrence roles → Tracked roles → Prop
  | administrative (focus : Occurrence roles) (after : State roles) :
      GeneralNominalSharedSteps.Administrative registry before.current focus after →
      At registry before focus {before with current := after}
  | install (packet : Packet roles) (support : List (Occurrence roles)) :
      GeneralNominalFeedbackSteps.Installable registry before.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet → PacketGuard before packet support →
      At registry before packet.site.occurrence (GeneralNominalSharedSteps.install before packet support)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      first ∈ before.current.sites → last ∈ before.current.sites →
      GeneralNominalFeedbackSites.SameInputs before.current first last →
      ¬ Alias before.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before first last support →
      At registry before first.occurrence (GeneralNominalSharedSteps.merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At registry before focus after

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context : GeneralNominalCandidates.Context) :
      GeneralNominalSourceFormation.InitialSource registry context root → SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem at_shared (action : At registry before focus after) :
    GeneralNominalSharedSteps.At registry before focus after := by
  cases action with
  | administrative focus after action => exact .administrative focus after action
  | install packet support enabled novel guard => exact .install packet support enabled novel guard.1
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem step_shared (step : Step registry root before after) :
    GeneralNominalSharedSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,at_shared step.choose_spec.2⟩

theorem formed_shared (formed : SourceFormed registry root state) :
    GeneralNominalSharedSteps.SourceFormed registry root state := by
  induction formed with
  | initial context source => exact .initial context source
  | update previous step ih => exact .update ih (step_shared step)

theorem tested_cycle_blocks (member : (origin,test) ∈ (inspection state.current packet).tests)
    (cycle : Cyclic state.current origin) : ¬ PacketGuard state packet support :=
  fun guard => (guard.2.1.2 _ member).2 cycle

theorem missing_location_blocks (member : (origin,test) ∈ (inspection state.current packet).tests)
    (missing : ¬ Located state.current origin) : ¬ PacketGuard state packet support :=
  fun guard => missing (guard.2.1.2 _ member).1

theorem missing_origin_blocks
    (missing : (inspection state.current packet).inspected.length ≠ (inspection state.current packet).tests.length) :
    ¬ PacketGuard state packet support := fun guard => missing guard.2.1.1

theorem alternative_cycle_blocks {roles : Roles.RoleDecls}
    {state : Tracked roles} {packet : Packet roles} {support : List (Occurrence roles)}
    {bounds : List (GeneralNominalInspection.Bounds state.current.context.state)}
    (visible : declaration ∈ packet.registry.declarations)
    (checked : DeclarationChecked packet.registry.constructors roles declaration)
    (role : declaration.role = packet.site.occurrence.demand.role)
    (ready : GeneralNominalRecursiveCandidates.HeadReady packet.registry state.current.context packet.site.occurrence declaration)
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context packet.site.occurrence = some bounds)
    (member : (origin,test) ∈ (inspection state.current
      ⟨packet.registry,state.current.context,packet.site,declaration,checked,bounds⟩).tests)
    (cycle : Cyclic state.current origin) : ¬ PacketGuard state packet support := by
  intro guard
  exact (guard.2.2 declaration visible checked role ready bounds located).2 _ member |>.2 cycle

theorem safe_test (safe : Safe state packet) (member : (origin,test) ∈ (inspection state packet).tests)
    (represented : Represents state origin identity) : ¬ GeneralNominalFeedbackK2.RecursAt state identity :=
  fun cycle => (safe.2 _ member).2 ⟨identity,represented,cycle⟩

theorem accessible_of_shared
    (accessible : Acc (fun next current => GeneralNominalSharedSteps.Step registry root current next) state) :
    Acc (fun next current => Step registry root current next) state := by
  induction accessible with
  | intro state below ih => exact .intro state (fun next step => ih next (step_shared step))

end Yulang.GeneralNominalActualInspectionSteps
