import Yulang.GeneralDictionarySharedMetadata

/-! Recorded type source identities survive actual Shared steps, including
certified descriptor refresh. This is not an observation-completeness result. -/
namespace Yulang.GeneralDictionarySharedSourceRetention
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalIdentityLeaf
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def Retains (before after : GeneralNominalCandidates.Context) : Prop :=
  ∀ slot : Fin before.state.base.slots,
    ∃ next : Fin after.state.base.slots, after.state.base.source next = before.state.base.source slot

theorem retains_refl (context : GeneralNominalCandidates.Context) : Retains context context :=
  fun slot => ⟨slot,rfl⟩

theorem retains_trans {first middle last : GeneralNominalCandidates.Context}
    (one : Retains first middle) (two : Retains middle last) : Retains first last := by
  intro slot
  obtain ⟨mid,eq⟩ := one slot
  obtain ⟨next,eq'⟩ := two mid
  exact ⟨next,eq'.trans eq⟩

theorem step_retains {before after : Tracked roles}
    (step : GeneralNominalSharedSteps.Step registry root before after) :
    Retains before.current.context after.current.context := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue => exact retains_refl _
    | equate => exact retains_refl _
    | reobserve => exact retains_refl _
    | refresh context certificate source member unknown known =>
      intro slot
      exact ⟨certificate.refines.base.embed slot,certificate.refines.base.source slot⟩
  | install packet support enabled novel guard =>
    rw [← enabled.1.2.1]
    intro slot
    exact ⟨slot,rfl⟩
  | merge => exact retains_refl _

theorem recorded_sources {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets, Retains packet.context state.current.context := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed step ih =>
    have growth := step_retains step
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      have packets : after.packets = before.current.packets := by cases action <;> rfl
      intro packet member
      exact retains_trans (ih packet (packets ▸ member)) growth
    | install added support enabled novel guard =>
      intro packet member
      change packet ∈ added :: before.current.packets at member
      rcases List.mem_cons.mp member with same | old
      · subst packet
        rw [enabled.1.2.1]
        exact growth
      · exact retains_trans (ih packet old) growth
    | merge =>
      intro packet member
      exact retains_trans (ih packet member) growth

theorem identity_current_evidence {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (shape : Shape packet.declaration) (input : Nat)
    (point : Point packet.site.occurrence input)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model
      packet.site.occurrence (.node packet.declaration.id []) := by
  have located := (GeneralDictionarySharedRecordedEvidence.formed_recorded formed packet member).1.2.2.2.1
  obtain ⟨old,_,source⟩ := located_point point located
  obtain ⟨slot,same⟩ := recorded_sources formed packet member old
  exact GeneralDictionarySharedMetadata.identity_current_evidence formed packet member shape input point
    slot (same.trans source) model valid

end Yulang.GeneralDictionarySharedSourceRetention
