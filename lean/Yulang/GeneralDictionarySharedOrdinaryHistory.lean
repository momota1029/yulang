import Yulang.GeneralDictionarySharedRecordedTree

/-! An ordinary-context restriction of the actual Shared source history.
The restriction is an exact context shape, not an Evidence premise. It excludes
unrestricted descriptor refresh and does not assert existence of a recorded tree. -/
namespace Yulang.GeneralDictionarySharedOrdinaryHistory
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryOrdinaryTrace (Extension extension_trans)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : Tracked roles}

inductive Formed (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context : GeneralNominalCandidates.Context) :
      GeneralNominalSourceFormation.InitialSource registry context root →
      Formed registry root (initial context root)
  | update : Formed registry root before →
      GeneralNominalSharedSteps.Step registry root before after →
      Extension before.current.context after.current.context → Formed registry root after

theorem source_formed (formed : Formed registry root state) :
    GeneralNominalSharedSteps.SourceFormed registry root state := by
  induction formed with
  | initial context source => exact .initial context source
  | update before step growth ih => exact .update ih step

theorem recorded_growth (formed : Formed registry root state) :
    ∀ packet ∈ state.current.packets, Extension packet.context state.current.context := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed step growth ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      have packets : after.packets = before.current.packets := by cases action <;> rfl
      intro packet member
      exact extension_trans (ih packet (packets ▸ member)) growth
    | install added support enabled novel guard =>
      intro packet member
      change packet ∈ added :: before.current.packets at member
      rcases List.mem_cons.mp member with same | old
      · subst packet
        exact GeneralDictionaryOrdinaryTrace.packet_extension added
      · exact extension_trans (ih packet old) growth
    | merge first last support one two same novel guard =>
      intro packet member
      exact extension_trans (ih packet member) growth

/-- Every actual Shared installation has ordinary context growth. -/
theorem install_extension (state : Tracked roles) (packet : Packet roles)
    (support : List (Occurrence roles)) (same : packet.context = state.current.context) :
    Extension state.current.context
      (GeneralNominalSharedSteps.install state packet support).current.context := by
  change Extension state.current.context packet.privateContext
  rw [← same]
  exact GeneralDictionaryOrdinaryTrace.packet_extension packet

/-- A real install step can extend the restricted history without an extra
transport hypothesis. Its existing guards and freshness are not weakened. -/
theorem installed (formed : Formed registry root state)
    (packet : Packet roles) (support : List (Occurrence roles))
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support) :
    Formed registry root (GeneralNominalSharedSteps.install state packet support) :=
  .update formed ⟨packet.site.occurrence, generated, .install packet support enabled novel guard⟩
    (install_extension state packet support enabled.1.2.1)

theorem current_evidence (formed : Formed registry root state)
    (tree : GeneralDictionarySharedRecordedTree.RecordedTree state.current occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload :=
  GeneralDictionarySharedRecordedTree.current_evidence (source_formed formed)
    (recorded_growth formed) tree model valid

end Yulang.GeneralDictionarySharedOrdinaryHistory
