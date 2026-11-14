import Yulang.GeneralNominalCenteredRegistryJournal

/-! The fixed executor chooses from the literal set of terminal snapshots.
Its order field reduces to packet-free shared inputs with an enabled action. -/
namespace Yulang.GeneralNominalCenteredFixedChoice
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalCenteredAdministrativeComposition
open GeneralNominalCenteredGroundComposition (terminalState terminalState_exact)

variable {roles : Roles.RoleDecls}

def Exit (registry : Registry) (state : State roles) (root : Occurrence roles)
    (final : State roles) : Prop :=
  B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next

def Certificate (registry : Registry) (state : State roles) (root : Occurrence roles)
    (final : State roles) : Prop :=
  B4Target.Steps (Step registry root) state final ∧
    (∀ next, ¬ Step registry root final next) ∧ Stable registry final root ∧
    (∀ child, GeneralNominalSaturationState.Generated final.erased.current root child → Stable registry final child) ∧
    ∀ model, Models final model → Models state model

theorem certificate_iff_exit (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (final : State roles) : Certificate registry state root final ↔ Exit registry state root final := by
  constructor
  · intro certificate; exact ⟨certificate.1,certificate.2.1⟩
  · rintro ⟨path,stopped⟩
    have stable := closure registry checked final root
      (B4TargetV5.reachable_steps (boundary roles) reachable path) stopped
    exact ⟨path,stopped,stable.1,stable.2,
      B4SkeletonV5.steps_models (boundary roles) registry root (stepModels registry checked root) reachable path⟩

theorem exit_exists (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    ∃ final, Exit registry state root final := by
  obtain ⟨final,certificate⟩ := GeneralNominalCenteredGroundBoundary.terminal registry checked state root reachable
  exact ⟨final,certificate.1,certificate.2.1⟩

theorem choose_congr {α : Sort u} {first last : α → Prop}
    (one : ∃ value, first value) (two : ∃ value, last value)
    (same : ∀ value, first value ↔ last value) : Classical.choose one = Classical.choose two := by
  have equal : first = last := funext (fun value => propext (same value))
  cases equal
  rfl

theorem terminalState_eq_choose_exit (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (existsExit : ∃ final, Exit registry state root final) :
    terminalState registry state root = Classical.choose existsExit := by
  rw [terminalState_exact registry checked state root reachable]
  exact choose_congr (GeneralNominalCenteredGroundBoundary.terminal registry checked state root reachable)
    existsExit (certificate_iff_exit checked reachable)

theorem terminalState_eq_of_exit_iff
    (checked : (boundary roles).Checked first) (checkedLast : (boundary roles).Checked last)
    (reached : B4TargetV5.Reachable (boundary roles) first root state)
    (reachedLast : B4TargetV5.Reachable (boundary roles) last root state)
    (same : ∀ final, Exit first state root final ↔ Exit last state root final) :
    terminalState first state root = terminalState last state root := by
  rw [terminalState_eq_choose_exit checked reached (exit_exists checked reached),
    terminalState_eq_choose_exit checkedLast reachedLast (exit_exists checkedLast reachedLast)]
  exact choose_congr _ _ same

theorem steps_from_halted {α : Type u} {relation : α → α → Prop}
    {start final : α} (stopped : ∀ next, ¬ relation start next)
    (path : B4Target.Steps relation start final) : final = start := by
  induction path with
  | refl => rfl
  | tail path step ih => exact False.elim (stopped _ (ih ▸ step))

theorem terminalState_eq_of_halted (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (stopped : ∀ next, ¬ Step registry root state next) :
    terminalState registry state root = state :=
  steps_from_halted stopped (execution registry checked state root reachable)

theorem fixed_local_of_shared_packet
    (reached : B4TargetV5.Reachable (boundary roles) first root state)
    (reachedLast : B4TargetV5.Reachable (boundary roles) last root state)
    (recorded : packet ∈ state.erased.current.packets) (demand : Occurrence roles) (frontier) :
    Local last (terminalState first state root) demand frontier ↔
      Local last (terminalState last state root) demand frontier := by
  rw [GeneralNominalCenteredRegistryJournal.shared_packet_registry reached reachedLast recorded]

theorem fixed_local_of_halted
    (checked : (boundary roles).Checked first) (checkedLast : (boundary roles).Checked last)
    (reached : B4TargetV5.Reachable (boundary roles) first root state)
    (reachedLast : B4TargetV5.Reachable (boundary roles) last root state)
    (stopped : ∀ next, ¬ Step first root state next)
    (stoppedLast : ∀ next, ¬ Step last root state next) (demand : Occurrence roles) (frontier) :
    Local last (terminalState first state root) demand frontier ↔
      Local last (terminalState last state root) demand frontier := by
  rw [terminalState_eq_of_halted checked reached stopped,
    terminalState_eq_of_halted checkedLast reachedLast stoppedLast]

/-- Choice coherence is required only before a shared input records a packet,
and only when at least one registry can advance it. -/
def PacketFreeExitChoiceAgreement (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last →
    (boundary roles).Reorders first last → first ≠ last → ∀ state root,
    B4TargetV5.Reachable (boundary roles) first root state →
    B4TargetV5.Reachable (boundary roles) last root state → state.erased.current.packets = [] →
    ((∃ next, Step first root state next) ∨ ∃ next, Step last root state next) →
    ∀ (left : ∃ final, Exit first state root final) (right : ∃ final, Exit last state root final)
      demand frontier,
      Local last (Classical.choose left) demand frontier ↔ Local last (Classical.choose right) demand frontier

theorem final_local_iff_packet_free_choice :
    FinalLocalAgreement roles ↔ PacketFreeExitChoiceAgreement roles := by
  constructor
  · intro agreement first last checked checkedLast order _ state root reached reachedLast _ _ left right demand frontier
    rw [← terminalState_eq_choose_exit checked reached left,
      ← terminalState_eq_choose_exit checkedLast reachedLast right]
    exact agreement first last checked checkedLast order state root reached reachedLast demand frontier
  · intro agreement first last checked checkedLast order state root reached reachedLast demand frontier
    classical
    by_cases same : first = last
    · subst last; exact Iff.rfl
    · have empty := GeneralNominalCenteredRegistryJournal.distinct_shared_packet_free same reached reachedLast
      by_cases advances : (∃ next, Step first root state next) ∨ ∃ next, Step last root state next
      · rw [terminalState_eq_choose_exit checked reached (exit_exists checked reached),
          terminalState_eq_choose_exit checkedLast reachedLast (exit_exists checkedLast reachedLast)]
        exact agreement first last checked checkedLast order same state root reached reachedLast empty advances
          _ _ demand frontier
      · exact fixed_local_of_halted checked checkedLast reached reachedLast
          (fun next step => advances (.inl ⟨next,step⟩))
          (fun next step => advances (.inr ⟨next,step⟩)) demand frontier

theorem canonicalLocalOrder_iff_packet_free_choice :
    CanonicalLocalOrder roles ↔ PacketFreeExitChoiceAgreement roles :=
  canonicalLocalOrder_iff_final_local_agreement.trans final_local_iff_packet_free_choice

theorem canonicalLocalOrder_of_packet_free_choice
    (agreement : PacketFreeExitChoiceAgreement roles) : CanonicalLocalOrder roles :=
  canonicalLocalOrder_iff_packet_free_choice.mpr agreement

end Yulang.GeneralNominalCenteredFixedChoice
