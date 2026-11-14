import Yulang.GeneralNominalCenteredPacketFreeJoint
import Yulang.GeneralNominalPacketMetadata
import Yulang.GeneralNominalCenteredPlanLedgerReordering
import Yulang.GeneralNominalValuePermutation

/-! A finite common pairing table gives the concrete representation intended
for canonical transport. Each paired packet is a registry/declaration rebase
followed by replacement of metadata enumeration with the same membership. -/
namespace Yulang.GeneralNominalCenteredPermutationRepresentation
open GeneralDeclarations GeneralRegistryReordering GeneralNominalSaturationState
open GeneralNominalLedgerPermutation (PacketObservation)

variable {roles : Roles.RoleDecls}

def RebasedPacket (first last : Registry) (packet other : Packet roles) : Prop :=
  packet.registry = first ∧ ∃ declaration, ∃ order : Reorders packet.registry last,
    ∃ pair : DeclarationReorders packet.declaration declaration,
    ∃ allocated reserved,
      (∀ key, key ∈ allocated ↔ key ∈ packet.context.state.allocated) ∧
      (∀ name, name ∈ reserved ↔ name ∈ packet.context.state.reserved) ∧
      other = GeneralNominalPacketMetadata.rebase (GeneralNominalPacketReordering.rebase packet order pair) allocated reserved

theorem packet_observation {packet other : Packet roles} (paired : RebasedPacket first last packet other) (roleEq : first.roles = roles) :
    PacketObservation packet other := by
  obtain ⟨registry,decl,order,pair,allocated,reserved,_,_,rfl⟩ := paired
  have one := PacketObservation.rebase packet order pair (registry ▸ roleEq)
  have two := GeneralNominalPacketMetadata.observation (GeneralNominalPacketReordering.rebase packet order pair) allocated reserved
  exact ⟨⟨one.site.trans two.site,one.children.trans two.children,one.identity.trans two.identity,
      fun model => (one.holds model).trans (two.holds model),
      fun model => (one.toPacketPair.inputs model).trans (two.toPacketPair.inputs model),
      fun model => (one.toPacketPair.outputs model).trans (two.toPacketPair.outputs model)⟩,
    fun observation => (one.reads observation).trans (two.reads observation),
    one.named.trans two.named,one.input.trans two.input,one.outputNames.trans two.outputNames,one.capture.trans two.capture,
    fun models name origin => (one.captured models name origin).trans (two.captured models name origin)⟩

def paired (table : List (Packet roles × Packet roles)) (first last : Packet roles) : Prop := (first,last) ∈ table

def Corresponds (first last : Registry) (left right : GeneralNominalCenteredSteps.State roles) : Prop :=
  ∃ table : List (Packet roles × Packet roles),
    (∀ packet other, paired table packet other → RebasedPacket first last packet other) ∧
    (∀ packet other, paired table packet other → packet ∈ left.erased.current.packets ∧ other ∈ right.erased.current.packets) ∧
    GeneralNominalCenteredLedgerPermutation.Related (paired table) left right

theorem packet_free_refl (first last : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (packets : state.erased.current.packets = []) (facts : state.erased.facts = []) (plans : state.plans = []) :
    Corresponds first last state state := by
  refine ⟨[],(by intro _ _ impossible; cases impossible),(by intro _ _ impossible; cases impossible),?_⟩
  refine ⟨⟨⟨(by intro _ _ _ impossible; cases impossible),
      (by intro _ _ _ impossible; cases impossible),(by intro _ _ impossible; cases impossible)⟩,
    rfl,GeneralNominalJournalPermutation.Related.refl _,?_,?_⟩,fun _ => Iff.rfl,?_,rfl⟩
  · intro _ _ _; simp only [packets,List.not_mem_nil]
  · rw [facts]; exact .nil
  · rw [plans]; exact .nil

theorem initialAt (first last : Registry) (context) (site : GeneralNominalCenters.Site roles) :
    Corresponds first last (GeneralNominalCenteredSteps.initialAt context site) (GeneralNominalCenteredSteps.initialAt context site) :=
  packet_free_refl first last _ rfl rfl rfl

theorem initial (first last : Registry) (context) (root : GeneralSourceDictionaries.Occurrence roles) :
    Corresponds first last (GeneralNominalCenteredSteps.initial context root) (GeneralNominalCenteredSteps.initial context root) :=
  packet_free_refl first last _ rfl rfl rfl


variable {left right next : GeneralNominalCenteredSteps.State roles}

theorem at_transport_or_install
    (same : Corresponds first last left right)
    (action : GeneralNominalCenteredSteps.At first left focus next) :
    (∃ other, GeneralNominalCenteredSteps.At last right focus other ∧ Corresponds first last next other) ∨
      ∃ plan support, focus = plan.packet.site.occurrence ∧ next = GeneralNominalCenteredSteps.install left plan support ∧
        GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet ∧
        ¬ GeneralNominalFeedbackSteps.Committed left.erased.current plan.packet ∧ GeneralNominalCenteredSteps.PacketGuard left plan support := by
  obtain ⟨table,rebased,recorded,pair⟩ := same
  rcases pair.at_transport_or_install action last with ⟨other,step,pair⟩ | install
  · exact Or.inl ⟨other,step,table,rebased,fun packet target member =>
      ⟨GeneralNominalCenteredRegistryJournal.packet_at action (recorded packet target member).1,
        GeneralNominalCenteredRegistryJournal.packet_at step (recorded packet target member).2⟩,pair⟩
  · exact Or.inr install

theorem step_transport_or_install
    (same : Corresponds first last left right)
    (step : GeneralNominalCenteredSteps.Step first root left next) :
    (∃ other, GeneralNominalCenteredSteps.Step last root right other ∧ Corresponds first last next other) ∨
      ∃ plan support, GeneralNominalSaturationState.Generated left.erased.current root plan.packet.site.occurrence ∧
        next = GeneralNominalCenteredSteps.install left plan support ∧
        GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet ∧
        ¬ GeneralNominalFeedbackSteps.Committed left.erased.current plan.packet ∧ GeneralNominalCenteredSteps.PacketGuard left plan support := by
  obtain ⟨focus,generated,action⟩ := step
  rcases at_transport_or_install same action with ⟨other,step,pair⟩ | ⟨plan,support,equal,installed,enabled,novel,guard⟩
  · obtain ⟨_,_,_,before⟩ := same
    exact Or.inl ⟨other,⟨focus,(before.erased.current.generated root focus).mp generated,step⟩,pair⟩
  · exact Or.inr ⟨plan,support,equal ▸ generated,installed,enabled,novel,guard⟩


theorem packet_free_facts {state : GeneralNominalCenteredSteps.State roles}
    (path : B4Target.Steps (GeneralNominalCenteredSteps.Step registry root)
      (GeneralNominalCenteredSteps.initial context root) state)
    (empty : state.erased.current.packets = []) : state.erased.facts = [] := by
  induction path with
  | refl => rfl
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    have prior : before.erased.current.packets = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro packet member
      have retained := GeneralNominalCenteredRegistryJournal.packet_at action member
      rw [empty] at retained
      cases retained
    have facts := ih prior
    cases action with
    | administrative => exact facts
    | refresh => exact facts
    | install => cases empty
    | merge first last support one two same novel guard =>
      have shape := GeneralNominalCenteredPacketFreeJoint.packet_free_trace path prior
      rw [shape.1] at one two
      have firstEq := List.mem_singleton.mp one
      have lastEq := List.mem_singleton.mp two
      subst first; subst last
      exact False.elim (novel (.refl _))

theorem reachable_packet_free (last : Registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) first root state)
    (empty : state.erased.current.packets = []) : Corresponds first last state state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact packet_free_refl first last state empty (packet_free_facts path empty)
    (GeneralNominalCenteredPacketFreeJoint.packet_free_trace path empty).2.1

end Yulang.GeneralNominalCenteredPermutationRepresentation
