import Yulang.GeneralDictionarySupportJournal
import Yulang.GeneralDictionaryJointEquality

/-! Journal-key coherence without current-context packet equality. Installation
and administrative reobservation preserve coherence. An actual empty final alias
ledger excludes every merge and gives the invariant from InitialSource. The
simultaneous model half of Joint remains a separate semantic obligation. -/
namespace Yulang.GeneralDictionarySupportChoices
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

def Coherent (state : State roles) : Prop :=
  ∀ first ∈ state.packets, ∀ last ∈ state.packets,
    Alias state first.site.occurrence.identity last.site.occurrence.identity →
      first.declaration.id = last.declaration.id

theorem administrative_coherent (registry : Registry) (before after : State roles)
    (focus : Occurrence roles) (update : Administrative registry before focus after)
    (coherent : Coherent before) : Coherent after := by
  have packets : before.packets = after.packets := by cases update <;> rfl
  have aliases : after.aliases = before.aliases := by cases update <;> rfl
  intro first one last two related
  exact coherent first (packets ▸ one) last (packets ▸ two)
    (GeneralDictionaryJointEquality.alias_same (before := after) (after := before) aliases related)

theorem install_coherent (registry : Registry) (before : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (coherent : Coherent before.current) : Coherent (install before packet support).current := by
  intro first one last two related
  have old : Alias before.current first.site.occurrence.identity last.site.occurrence.identity :=
    GeneralDictionaryJointEquality.alias_same (before := (install before packet support).current) (after := before.current) rfl related
  have choices := (GeneralNominalCycleSteps.installable_joint enabled.1).1
  change first ∈ packet :: before.current.packets at one
  change last ∈ packet :: before.current.packets at two
  rcases List.mem_cons.mp one with firstNew | firstOld
  · subst first
    rcases List.mem_cons.mp two with lastNew | lastOld
    · subst last; rfl
    · exact (choices last lastOld old).symm
  · rcases List.mem_cons.mp two with lastNew | lastOld
    · subst last
      exact choices first firstOld old.symm
    · exact coherent first firstOld last lastOld old

/-- No merge can be hidden in a trace whose final alias list is empty. -/
theorem formed_aliasFree_coherent (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (empty : state.current.aliases = []) : Coherent state.current := by
  induction formed with
  | initial context source => intro first member; cases member
  | update formed update ih =>
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | administrative _ _ admin =>
      apply administrative_coherent _ _ _ _ admin
      apply ih
      cases admin <;> exact empty
    | install packet support enabled novel guard =>
      exact install_coherent _ _ packet support enabled (ih empty)
    | merge => cases empty

/-- A known recorded key determines every key in its alias class; unlike
Current, this assertion does not re-run the packet's observation report. -/
theorem recorded_class_key (state : State roles) (coherent : Coherent state)
    (focus : Occurrence roles) (chosen : Packet roles) (recorded : chosen ∈ state.packets)
    (same : chosen.site.occurrence.identity = focus.identity) :
    ∀ packet ∈ state.packets, Alias state focus.identity packet.site.occurrence.identity →
      packet.declaration.id = chosen.declaration.id := by
  intro packet member related
  exact (coherent chosen recorded packet member (same ▸ related)).symm

end Yulang.GeneralDictionarySupportChoices
