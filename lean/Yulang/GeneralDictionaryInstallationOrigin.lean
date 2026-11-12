import Yulang.GeneralDictionarySupportJournal
import Yulang.GeneralDictionarySupportEvidence

/-! Exact operational origins for actual support-journal packets. Historical
coverage does not identify a current selected branch with a stored packet. -/
namespace Yulang.GeneralDictionaryInstallationOrigin
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

/-- The packet was genuinely installed at a generated focus, with the actual
support guard and installation conditions, and the complete later suffix. -/
def Origin (registry : Registry) (root : Occurrence roles)
    (finish : Tracked roles) (packet : Packet roles) : Prop :=
  ∃ before : Tracked roles, ∃ support : List (Occurrence roles),
    SourceFormed registry root before ∧
    Generated before.current root packet.site.occurrence ∧
    GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
    ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
    PacketGuard before packet support ∧
    B4Target.Steps (Step registry root) (GeneralNominalSupportSteps.install before packet support) finish

theorem origin_step {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles} {packet : Packet roles}
    (origin : Origin registry root before packet) (update : Step registry root before after) :
    Origin registry root after packet := by
  obtain ⟨start,support,formed,generated,enabled,fresh,guard,path⟩ := origin
  exact ⟨start,support,formed,generated,enabled,fresh,guard,.tail path update⟩

/-- Arbitrary source-formed history, without stability, selection, Joint or
current-context equality assumptions. -/
theorem packet_origin (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets, Origin registry root state packet := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed update ih =>
    have retain : ∀ packet ∈ before.current.packets, Origin registry root after packet :=
      fun packet member => origin_step (ih packet member) update
    obtain ⟨focus,generated,action⟩ := update
    intro packet member
    cases action with
    | administrative _ _ admin => cases admin <;> exact retain packet member
    | merge => exact retain packet member
    | install installed support enabled fresh guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact ⟨before,support,formed,generated,enabled,fresh,guard,.refl⟩
      · exact retain packet old

theorem steps_generated {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles} (path : B4Target.Steps (Step registry root) before after)
    {focus : Occurrence roles} (generated : Generated before.current root focus) :
    Generated after.current root focus := by
  induction path with
  | refl => exact generated
  | tail prior update ih => exact generated_monotone update ih

/-- Stored packet occurrences, not only their historical children, are genuine
members of the root-generated graph. -/
theorem packet_generated (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) :
    Generated state.current root packet.site.occurrence := by
  obtain ⟨before,support,_,generated,enabled,fresh,guard,path⟩ := packet_origin registry root state formed packet member
  exact steps_generated path (generated_monotone ⟨_,generated,.install packet support enabled fresh guard⟩ generated)

theorem step_packets {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles} (update : Step registry root before after)
    {packet : Packet roles} (member : packet ∈ before.current.packets) :
    packet ∈ after.current.packets := by
  obtain ⟨focus,generated,action⟩ := update
  cases action with
  | administrative _ _ admin => cases admin <;> exact member
  | merge => exact member
  | install => exact List.mem_cons_of_mem _ member

theorem steps_packets {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles} (path : B4Target.Steps (Step registry root) before after)
    {packet : Packet roles} (member : packet ∈ before.current.packets) :
    packet ∈ after.current.packets := by
  induction path with
  | refl => exact member
  | tail prior update ih => exact step_packets update ih

theorem origin_member {registry : Registry} {root : Occurrence roles}
    {state : Tracked roles} {packet : Packet roles} (origin : Origin registry root state packet) :
    packet ∈ state.current.packets := by
  obtain ⟨before,support,_,_,_,_,_,path⟩ := origin
  exact steps_packets path (List.mem_cons_self ..)

/-- Exact journal provenance. No arbitrary packet can be postulated as an
installation origin unless it occurs in the actual final journal. -/
theorem member_iff_origin (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) (packet : Packet roles) :
    packet ∈ state.current.packets ↔ Origin registry root state packet :=
  ⟨packet_origin registry root state formed packet, origin_member⟩

/-- The historical branch is true at the same caller assignment. This still
uses the stored packet context, never a substituted final observation. -/
theorem origin_holds {registry : Registry} {root : Occurrence roles}
    {state : Tracked roles} {packet : Packet roles} (origin : Origin registry root state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    packet.Holds model := valid.2.1 packet (origin_member origin)

/-- Nonterminal stable selection forces some real earlier guarded installation.
It does NOT prove that the installed occurrence/key matches this selection. -/
theorem nonterminal_origin (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (reached : focus = root ∨ Generated state.current root focus) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (nonterminal : children ≠ []) : ∃ packet, Origin registry root state packet := by
  obtain ⟨packet,member⟩ := GeneralDictionarySupportEvidence.nonterminal_has_packet registry root focus state
    reachable reached key children stable selected nonterminal
  exact ⟨packet,packet_origin registry root state
    (GeneralNominalSupportBoundary.reachable_formed registry state root reachable) packet member⟩

/-- Recover the complete initial-source prefix, not merely an inductive
source-formation certificate. -/
theorem formed_prefix (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∃ context : GeneralNominalCandidates.Context,
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state := by
  induction formed with
  | initial context source => exact ⟨context,source,.refl⟩
  | update formed update ih =>
    obtain ⟨context,source,path⟩ := ih
    exact ⟨context,source,.tail path update⟩

/-- Complete initial-prefix / selected-installation / final-suffix factorization
of every recorded packet. Local selection is historical, not final. -/
theorem packet_history (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) :
    ∃ context : GeneralNominalCandidates.Context, ∃ before : Tracked roles,
      ∃ support : List (Occurrence roles),
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) before ∧
      Generated before.current root packet.site.occurrence ∧
      packet.context = before.current.context ∧
      GeneralNominalSupportBoundary.Local registry before packet.site.occurrence
        (.selected packet.declaration.id packet.children) ∧
      GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
      PacketGuard before packet support ∧
      B4Target.Steps (Step registry root) (GeneralNominalSupportSteps.install before packet support) state := by
  obtain ⟨before,support,prior,generated,enabled,fresh,guard,path⟩ :=
    packet_origin registry root state formed packet member
  obtain ⟨context,source,priorPath⟩ := formed_prefix registry root before prior
  exact ⟨context,before,support,source,priorPath,generated,enabled.1.2.1,
    GeneralNominalSupportBoundary.install_selected packet enabled support guard,
    enabled,fresh,guard,path⟩

end Yulang.GeneralDictionaryInstallationOrigin
