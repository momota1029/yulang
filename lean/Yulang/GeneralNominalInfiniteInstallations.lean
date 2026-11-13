import Yulang.GeneralNominalValueSteps
import Yulang.GeneralNominalDownstreamOrder

/-! A precise necessary shape of an infinite trace of the current value-guarded
relation. Novel means uncommitted semantic facts or child edges; it does not
mean that the occurrence identity has never been installed before. -/
namespace Yulang.GeneralNominalInfiniteInstallations
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalValueSteps

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

private theorem trace_formed (trace : Nat → Tracked roles)
    (initial : SourceFormed registry root (trace 0))
    (steps : ∀ n, Step registry root (trace n) (trace (n+1))) :
    ∀ n, SourceFormed registry root (trace n) := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih => exact .update ih (steps n)

private theorem no_passive_tail (trace : Nat → Tracked roles) (cutoff : Nat)
    (updates : ∀ n, cutoff ≤ n → Passive registry root (trace n) (trace (n+1))) : False := by
  have excludes : ∀ state, Acc (fun next current => Passive registry root current next) state →
      ∀ n, cutoff ≤ n → state = trace n → False := by
    intro state accessible
    induction accessible with
    | intro state below ih =>
      intro n bounded equal
      subst state
      exact ih (trace (n+1)) (updates n bounded) (n+1) (by omega) rfl
  exact excludes (trace cutoff) (passive_accessible registry root _) cutoff (Nat.le_refl _) rfl

/-- Beyond every cutoff there is an enabled, guarded, uncommitted installation.
No scheduler or fairness premise, and no installation budget, is assumed. -/
theorem infinitely_often_installation (trace : Nat → Tracked roles)
    (initial : SourceFormed registry root (trace 0))
    (steps : ∀ n, Step registry root (trace n) (trace (n+1))) (cutoff : Nat) :
    ∃ n, cutoff ≤ n ∧ ∃ packet : Packet roles, ∃ support,
      Generated (trace n).current root packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry (trace n).current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed (trace n).current packet ∧
      PacketGuard (trace n) packet support ∧ trace (n+1) = install (trace n) packet support := by
  classical
  apply Classical.byContradiction
  intro absent
  apply no_passive_tail (registry := registry) (root := root) trace cutoff
  intro n bounded
  obtain ⟨focus,generated,action⟩ := steps n
  generalize laterEq : trace (n+1) = later at action
  cases action with
  | install packet support enabled novel guard =>
    exact False.elim (absent ⟨n,bounded,packet,support,generated,enabled,novel,guard,laterEq⟩)
  | merge first last support one two same novel guard =>
    exact ⟨⟨_,generated,.merge first last support one two same novel guard⟩,
      .ordinary (.merge first last one two same novel)⟩
  | administrative focus after action =>
    have given : Step registry root (trace n) {trace n with current := after} :=
      ⟨focus,generated,.administrative focus after action⟩
    cases action with
    | enqueue linked missing =>
      obtain ⟨site,member,equal⟩ := GeneralNominalSupportOrder.generated_registered
        (GeneralNominalDownstreamSteps.formed_old (formed_old (trace_formed trace initial steps n))) generated
      exact False.elim (missing site member equal)
    | refresh context certificate source member unknown known =>
      exact ⟨given,.ordinary (.refresh focus context certificate source member unknown known)⟩
    | equate first last one two equal novel =>
      exact ⟨given,.ordinary (.equate focus first last one two equal novel)⟩
    | reobserve revision certificate improved => exact ⟨given,.reobserve revision certificate improved⟩

end Yulang.GeneralNominalInfiniteInstallations
