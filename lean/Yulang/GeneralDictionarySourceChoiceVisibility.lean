import Yulang.GeneralDictionaryFeedbackEvidence
/-! Syntactic visibility invariant of the unchanged feedback formation trace.
This does not require a model witness and does not assume Joint or EvidenceNode. -/
namespace Yulang.GeneralDictionarySourceChoiceVisibility
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps
variable {roles : Roles.RoleDecls}

/-- Every recorded choice is an actual declaration of the current registry,
including in inconsistent journals where semantic visibility would be vacuous. -/
theorem visible (registry : Registry) (root : Occurrence roles) (state : State roles)
    (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.packets, packet.declaration ∈ registry.declarations := by
  induction formed with
  | initial context source => intro packet member; cases member
  | update formed update ih =>
    intro packet member
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | enqueue => exact ih packet member
    | merge => exact ih packet member
    | refresh => exact ih packet member
    | equate => exact ih packet member
    | install installed enabled novel =>
      rcases List.mem_cons.mp member with rfl | old
      · have member := enabled.1.2.2.2.1
        simpa only [enabled.1.1] using member
      · exact ih packet old

/-- A source-formed singleton registry cannot contain the invisible-key
obstruction, even before considering aliases or assuming inhabitedness. -/
theorem singleton_choice (registry : Registry) (root : Occurrence roles) (state : State roles)
    (formed : SourceFormed registry root state) (declaration : Declaration)
    (singleton : registry.declarations = [declaration]) :
    ∀ packet ∈ state.packets, packet.declaration = declaration := by
  intro packet member
  have recorded := visible registry root state formed packet member
  rw [singleton] at recorded
  exact List.mem_singleton.mp recorded

/-- First Joint conjunct follows in the singleton case. Its simultaneous-model
and per-alias applicability conjunct remains a distinct obligation. -/
theorem singleton_key_coherence (registry : Registry) (root : Occurrence roles) (state : State roles)
    (formed : SourceFormed registry root state) (declaration : Declaration)
    (singleton : registry.declarations = [declaration]) (focus : Occurrence roles) :
    ∀ packet ∈ state.packets, Alias state focus.identity packet.site.occurrence.identity →
      packet.declaration.id = declaration.id := by
  intro packet member _
  exact congrArg Declaration.id (singleton_choice registry root state formed declaration singleton packet member)
/-- The genuine current local classifier identifies the singleton key, so
coherence is with the selected key rather than a caller-chosen constant. -/
theorem singleton_selected_coherence (registry : Registry) (root : Occurrence roles) (state : State roles)
    (formed : SourceFormed registry root state) (declaration : Declaration)
    (singleton : registry.declarations = [declaration]) (focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    ∀ packet ∈ state.packets, Alias state focus.identity packet.site.occurrence.identity →
      packet.declaration.id = key := by
  have identity : declaration.id = key := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,candidate,member,_,identity,_⟩ := unique.1
      rw [singleton] at member
      have same := List.mem_singleton.mp member
      subst candidate
      exact identity
  intro packet member related
  exact (singleton_key_coherence registry root state formed declaration singleton focus packet member related).trans identity
end Yulang.GeneralDictionarySourceChoiceVisibility
