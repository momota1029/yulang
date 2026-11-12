import Yulang.GeneralDictionaryOrdinaryTrace
import Yulang.GeneralDictionaryInstallationOrigin
import Yulang.GeneralNominalSharedJournalPaths

/-! Allocation seed and ordinary equation provenance through every actual
support step, including observation-changing administrative updates. -/
namespace Yulang.GeneralDictionarySupportSourceInvariants
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

theorem administrative_seed {registry : Registry} {before after : State roles} {focus : Occurrence roles}
    (step : Administrative registry before focus after) : after.context.state.seed = before.context.state.seed := by
  cases step with
  | enqueue => rfl
  | refresh _ certificate => exact certificate.refines.seed
  | equate => rfl
  | reobserve => rfl

theorem administrative_ordinary {registry : Registry} {before after : State roles} {focus : Occurrence roles}
    (step : Administrative registry before focus after) :
    ∀ atom ∈ before.context.state.ordinary, atom ∈ after.context.state.ordinary := by
  cases step with
  | enqueue => exact fun _ member => member
  | refresh _ certificate => exact certificate.refines.ordinary
  | equate => exact fun _ member => List.mem_append_left _ member
  | reobserve => exact fun _ member => member

theorem step_seed {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (step : Step registry root before after) : after.current.context.state.seed = before.current.context.state.seed := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative _ _ update => exact administrative_seed update
  | install packet support enabled =>
    change packet.context.state.seed = before.current.context.state.seed
    exact congrArg (fun context => context.state.seed) enabled.1.2.1
  | merge => rfl

theorem step_ordinary {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (step : Step registry root before after) :
    ∀ atom ∈ before.current.context.state.ordinary, atom ∈ after.current.context.state.ordinary := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative _ _ update => exact administrative_ordinary update
  | install packet support enabled =>
    have growth := GeneralDictionaryOrdinaryTrace.install_extension before.current packet enabled.1.2.1
    obtain ⟨reserved,atoms,allocated,equal⟩ := growth
    change ∀ atom ∈ before.current.context.state.ordinary,
      atom ∈ (GeneralNominalFeedbackSites.install before.current packet (GeneralNominalFeedbackSites.emitted packet)).context.state.ordinary
    rw [equal]
    exact fun _ member => List.mem_append_left _ member
  | merge => exact fun _ member => List.mem_append_left _ member

theorem steps_seed {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) :
    after.current.context.state.seed = before.current.context.state.seed := by
  induction path with
  | refl => rfl
  | tail prior update ih => exact (step_seed update).trans ih

theorem steps_ordinary {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) :
    ∀ atom ∈ before.current.context.state.ordinary, atom ∈ after.current.context.state.ordinary := by
  induction path with
  | refl => exact fun _ member => member
  | tail prior update ih => exact fun atom member => step_ordinary update atom (ih atom member)

theorem recorded_path {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) {first last : Nat}
    (recorded : GeneralNominalSharedJournalPaths.RecordedPath before.current.context.state first last) :
    GeneralNominalSharedJournalPaths.RecordedPath after.current.context.state first last :=
  recorded.mono (steps_ordinary path)

/-- The old packet seed is not an independent semantic assumption. -/
theorem packet_seed (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state) (packet : Packet roles) (member : packet ∈ state.current.packets) :
    packet.context.state.seed = state.current.context.state.seed := by
  obtain ⟨before,support,_,_,_,_,_,path⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
  exact (steps_seed path).symm
end Yulang.GeneralDictionarySupportSourceInvariants
