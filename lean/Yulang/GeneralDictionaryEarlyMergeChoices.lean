import Yulang.GeneralDictionarySupportChoices

/-! A structural scheduling condition discharges journal-key coherence without
assuming any key equations, Current, a singleton registry, or an empty alias
ledger. It permits merging an already committed class with an uncommitted one.
This is a scoped result: the unrestricted support executor has not been proved
to obey this schedule, and the simultaneous semantic half of Joint is separate. -/
namespace Yulang.GeneralDictionaryEarlyMergeChoices
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionarySupportChoices
variable {roles : Roles.RoleDecls}

/-- No installed packet has an identity in this alias class. -/
def UncommittedClass (state : State roles) (identity : Nat) : Prop :=
  ∀ packet ∈ state.packets, ¬ Alias state identity packet.site.occurrence.identity

/-- Only a merge between TWO already committed classes needs a key comparison. -/
def Early (state : State roles) (first last : GeneralNominalDemandMerging.Site roles) : Prop :=
  UncommittedClass state first.occurrence.identity ∨
  UncommittedClass state last.occurrence.identity

theorem merge_coherent (state : State roles)
    (first last : GeneralNominalDemandMerging.Site roles)
    (before : Coherent state) (early : Early state first last) :
    Coherent (GeneralNominalSaturationState.merge state first last) := by
  apply GeneralDictionarySupportChoices.merge_coherent state first last before
  intro one oneMem two twoMem left right
  rcases early with empty | empty
  · exact False.elim (empty one oneMem left)
  · exact False.elim (empty two twoMem right)

/-- A checked operational trace, with a purely structural scheduling restriction
at merge steps. Every constructor is an actual support-aware transition. -/
inductive Scheduled (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context) (source : GeneralNominalSourceFormation.InitialSource registry context root) :
      Scheduled registry root (GeneralNominalSupport.initial context root)
  | administrative {before after} (prior : Scheduled registry root before)
      (focus) (generated : Generated before.current root focus)
      (action : Administrative registry before.current focus after) :
      Scheduled registry root {before with current := after}
  | install {before} (prior : Scheduled registry root before)
      (packet : Packet roles) (support : List (Occurrence roles))
      (generated : Generated before.current root packet.site.occurrence)
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
      (guard : PacketGuard before packet support) :
      Scheduled registry root (GeneralNominalSupportSteps.install before packet support)
  | merge {before} (prior : Scheduled registry root before)
      (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles))
      (generated : Generated before.current root first.occurrence)
      (one : first ∈ before.current.sites) (two : last ∈ before.current.sites)
      (same : GeneralNominalFeedbackSites.SameInputs before.current first last)
      (novel : ¬ Alias before.current first.occurrence.identity last.occurrence.identity)
      (guard : GeneralNominalSupportChoices.MergeGuard before first last support)
      (early : Early before.current first last) :
      Scheduled registry root (GeneralNominalSupportSteps.merge before first last support)

theorem scheduled_formed (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state) :
    SourceFormed registry root state := by
  induction path with
  | initial context source => exact .initial context source
  | administrative prior focus generated action ih =>
      exact .update ih ⟨focus,generated,.administrative focus _ action⟩
  | install prior packet support generated enabled novel guard ih =>
      exact .update ih ⟨packet.site.occurrence,generated,.install packet support enabled novel guard⟩
  | merge prior first last support generated one two same novel guard early ih =>
      exact .update ih ⟨first.occurrence,generated,.merge first last support one two same novel guard⟩

/-- All administrative updates, including certified point reobservation, and
all enabled installations remain unrestricted. No semantic key premise occurs. -/
theorem scheduled_coherent (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state) : Coherent state.current := by
  induction path with
  | initial context source => intro packet member; cases member
  | administrative prior focus generated action ih =>
      exact administrative_coherent registry _ _ focus action ih
  | install prior packet support generated enabled novel guard ih =>
      exact install_coherent registry _ packet support enabled ih
  | merge prior first last support generated one two same novel guard early ih =>
      exact merge_coherent _ first last ih early

/-- At a recorded root, the entire journal-key half of Joint is discharged for
this schedule, independently of current-context reinspection. -/
theorem recorded_choices (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (path : Scheduled registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (atFocus : packet.site.occurrence.identity = focus.identity) :
    ∀ prior ∈ state.current.packets, Alias state.current focus.identity prior.site.occurrence.identity →
      prior.declaration.id = packet.declaration.id :=
  recorded_class_key state.current (scheduled_coherent registry root state path)
    focus packet recorded atFocus

end Yulang.GeneralDictionaryEarlyMergeChoices
