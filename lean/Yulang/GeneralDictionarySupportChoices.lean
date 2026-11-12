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

/-- Adding one alias edge only joins its two old equivalence classes. -/
theorem alias_merge_cases (state : State roles) (first last : GeneralNominalDemandMerging.Site roles)
    (a b : Nat) (related : Alias (GeneralNominalSaturationState.merge state first last) a b) :
    Alias state a b ∨
      (Alias state a first.occurrence.identity ∧ Alias state last.occurrence.identity b) ∨
      (Alias state a last.occurrence.identity ∧ Alias state first.occurrence.identity b) := by
  induction related with
  | refl => exact Or.inl (.refl _)
  | edge member =>
    rcases List.mem_cons.mp member with added | old
    · have eq := Prod.mk.inj added
      cases eq.1; cases eq.2
      exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
    · exact Or.inl (.edge old)
  | symm _ ih =>
    rcases ih with old | ⟨left,right⟩ | ⟨left,right⟩
    · exact Or.inl old.symm
    · exact Or.inr (Or.inr ⟨right.symm,left.symm⟩)
    · exact Or.inr (Or.inl ⟨right.symm,left.symm⟩)
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with old | ⟨left,right⟩ | ⟨left,right⟩
    · rcases ih₂ with old₂ | ⟨left₂,right₂⟩ | ⟨left₂,right₂⟩
      · exact Or.inl (old.trans old₂)
      · exact Or.inr (Or.inl ⟨old.trans left₂,right₂⟩)
      · exact Or.inr (Or.inr ⟨old.trans left₂,right₂⟩)
    · rcases ih₂ with old₂ | ⟨left₂,right₂⟩ | ⟨left₂,right₂⟩
      · exact Or.inr (Or.inl ⟨left,right.trans old₂⟩)
      · exact Or.inr (Or.inl ⟨left,right₂⟩)
      · exact Or.inl (left.trans right₂)
    · rcases ih₂ with old₂ | ⟨left₂,right₂⟩ | ⟨left₂,right₂⟩
      · exact Or.inr (Or.inr ⟨left,right.trans old₂⟩)
      · exact Or.inl (left.trans right₂)
      · exact Or.inr (Or.inr ⟨left,right₂⟩)

/-- The exact additional key obligation is between the TWO classes being
merged, not a global Current or post-state coherence hypothesis. -/
theorem merge_coherent (state : State roles) (first last : GeneralNominalDemandMerging.Site roles)
    (coherent : Coherent state)
    (cross : ∀ one ∈ state.packets, ∀ two ∈ state.packets,
      Alias state first.occurrence.identity one.site.occurrence.identity →
      Alias state last.occurrence.identity two.site.occurrence.identity →
        one.declaration.id = two.declaration.id) :
    Coherent (GeneralNominalSaturationState.merge state first last) := by
  intro one member₁ two member₂ related
  rcases alias_merge_cases state first last _ _ related with old | ⟨left,right⟩ | ⟨left,right⟩
  · exact coherent one member₁ two member₂ old
  · exact cross one member₁ two member₂ left.symm right
  · exact (cross two member₂ one member₁ right left.symm).symm

private theorem alias_into_merge (state : State roles) (first last : GeneralNominalDemandMerging.Site roles)
    {a b : Nat} (related : Alias state a b) : Alias (GeneralNominalSaturationState.merge state first last) a b := by
  induction related with
  | refl => exact .refl _
  | edge member => exact .edge (List.mem_cons_of_mem _ member)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The two-class condition is necessary as well as sufficient. This does not
assert that the operational SameInputs/MergeGuard already supplies it. -/
theorem merge_coherent_iff (state : State roles) (first last : GeneralNominalDemandMerging.Site roles) :
    Coherent (GeneralNominalSaturationState.merge state first last) ↔
      Coherent state ∧ (∀ one ∈ state.packets, ∀ two ∈ state.packets,
        Alias state first.occurrence.identity one.site.occurrence.identity →
        Alias state last.occurrence.identity two.site.occurrence.identity →
          one.declaration.id = two.declaration.id) := by
  constructor
  · intro coherent
    constructor
    · intro one member₁ two member₂ related
      exact coherent one member₁ two member₂ (alias_into_merge state first last related)
    · intro one member₁ two member₂ fromFirst fromLast
      exact coherent one member₁ two member₂
        ((alias_into_merge state first last fromFirst).symm.trans
          ((Alias.edge (List.mem_cons_self)).trans (alias_into_merge state first last fromLast)))
  · rintro ⟨coherent,cross⟩
    exact merge_coherent state first last coherent cross

/-- The global journal invariant reduces to a check at actual enabled merges.
Administrative transitions and installations add no further residual. -/
theorem formed_coherent_of_merge_keys (registry : Registry) (root : Occurrence roles)
    (cross : ∀ (before : Tracked roles), SourceFormed registry root before →
      ∀ (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles)),
      Generated before.current root first.occurrence →
      first ∈ before.current.sites → last ∈ before.current.sites →
      GeneralNominalFeedbackSites.SameInputs before.current first last →
      ¬ Alias before.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before first last support →
      ∀ one ∈ before.current.packets, ∀ two ∈ before.current.packets,
      Alias before.current first.occurrence.identity one.site.occurrence.identity →
      Alias before.current last.occurrence.identity two.site.occurrence.identity →
        one.declaration.id = two.declaration.id)
    (state : Tracked roles) (formed : SourceFormed registry root state) : Coherent state.current := by
  induction formed with
  | initial context source => intro packet member; cases member
  | update formed update ih =>
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | administrative _ _ admin => exact administrative_coherent _ _ _ _ admin ih
    | install packet support enabled novel guard => exact install_coherent _ _ packet support enabled ih
    | merge first last support one two same novel guard =>
      exact merge_coherent _ first last ih (cross _ formed first last support generated one two same novel guard)

end Yulang.GeneralDictionarySupportChoices
