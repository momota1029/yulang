import Yulang.GeneralMixedCompoundEarlySquare308
import Yulang.GeneralMixedCompoundUpperTypes307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralMixedCompoundSourcePrefix308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot context source_bound alias_zero)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundFrame238 (before installed effect frame)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralMixedCompoundUpperTypes307 (kind meaning equiv_kind)
open GeneralNominalVersionedJournal232 (Models Effect State)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown no_refresh generated_only)
open GeneralNominalReobservationSteps (Revision Improves)
open GeneralNominalVersionedMixedObservations233 (Reobserve)
open GeneralNominalVersionedRefresh232 (reobserve)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem initial_model : Models before model := GeneralDictionaryCompoundStep238.old_model_initial

theorem initial_names (a : Nat) (ha : a ≤ 4) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega

theorem classified (n : Nat) (hn : n ≤ 4) : (model n).1 = meaning (kind n) := by
  rcases initial_names n hn with rfl|rfl|rfl|rfl|rfl <;> rfl

theorem full_same (a b : Nat) (one : a ≤ 4) (two : b ≤ 4)
    (semantic : GeneralNominalVersionedMixedKernel234.Equal before a b) :
    a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  have yes := semantic model initial_model
  rw [classified a one,classified b two] at yes
  have same := equiv_kind yes
  rcases initial_names a one with rfl|rfl|rfl|rfl|rfl <;>
    rcases initial_names b two with rfl|rfl|rfl|rfl|rfl <;>
    first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨rfl,rfl⟩)
          | exact Or.inr (Or.inr ⟨rfl,rfl⟩) | cases same

theorem equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed before := by
  intro a b one two semantic m valid
  rcases full_same a b (source_bound a one) (source_bound b two) semantic with
    rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact alias_zero m valid
  · have same := alias_zero m valid
    exact ⟨same.2,same.1⟩

theorem known_0 : GeneralNominalState.Known snapshot 0 :=
  ⟨(0 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_1 : GeneralNominalState.Known snapshot 1 :=
  ⟨(1 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_2 : GeneralNominalState.Known snapshot 2 :=
  ⟨(2 : Fin 5),rfl,Or.inl (by decide +kernel)⟩

theorem headless : HeadlessUnknown before := by
  refine ⟨model,initial_model,?_⟩
  intro n supported absent test seen
  rcases initial_names n (source_bound n supported) with rfl|rfl|rfl|rfl|rfl
  · exact absent known_0
  · exact absent known_1
  · exact absent known_2
  · exact GeneralDictionaryGroundCopy218Refresh.top_no_head test seen
  · exact GeneralDictionaryOptionalOutput229.no_test test seen

theorem identified_effect (e : Effect roles) (enabled : Installable registry before e)
    (rootFocus : e.plan.packet.site.occurrence = root) : e = effect := by
  have checked := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,rootFocus] at checked
  have exactPlan := GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl checked frame
  rcases e with ⟨reg,snapshot,plan,proof,picked,ready⟩
  dsimp only at exactPlan
  have registryEq : reg = registry := enabled.registry_eq
  have snapshotEq : snapshot = before.core := enabled.snapshot_eq
  subst reg; subst snapshot
  cases exactPlan
  rfl

noncomputable abbrev firstRevision := GeneralDictionaryVersionedReobserve233.revision
  (state := before) [] [] [] rfl
noncomputable abbrev pointBefore := GeneralDictionaryVersionedReobserve233.result
  (state := before) [] [] [] rfl

theorem early_reobservation : Step registry root before pointBefore :=
  GeneralNominalVersionedMixedKernel234.old_step (GeneralDictionaryVersionedReobserve233.step
    (state := before) rfl [] [] [] rfl registry root)

theorem reobserve_models (m : Assignment) : Models pointBefore m ↔ Models before m :=
  GeneralDictionaryVersionedReobserve233.models_iff (state := before) rfl [] [] [] rfl m

theorem two_steps :
    Step registry root before installed ∧ Step registry root before pointBefore ∧ installed ≠ pointBefore := by
  refine ⟨GeneralDictionaryCompoundStep238.step,early_reobservation,?_⟩
  intro same
  have lengths := congrArg (fun s : State roles => s.plans.length) same
  cases lengths

theorem exact_operation {t : State roles} : Step registry root before t ↔
    t = installed ∨ ∃ rev : Revision before.core.erased.current,
      Reobserve before rev ∧ Improves rev ∧ t = reobserve before rev := by
  constructor
  · rintro ⟨focus,generated,action⟩
    have rootIdentity := generated_only rfl rfl generated
    cases action with
    | administrative op =>
      cases op with
      | enqueue linked absent => exact (absent _ (List.mem_singleton_self _) rootIdentity.symm).elim
      | refresh ctx cert id member unknown known =>
        exact (no_refresh headless cert member unknown known).elim
      | equate a b one two semantic novel => exact (novel (equality_closed a b one two semantic)).elim
      | reobserve rev cert good => exact Or.inr ⟨rev,cert,good,rfl⟩
    | refresh _ ctx cert id present unknown known =>
      exact (no_refresh headless cert present unknown known).elim
    | install e enabled _ =>
      exact Or.inl (congrArg (GeneralNominalVersionedInstall232.install before)
        (identified_effect e enabled rootIdentity))
    | merge first last x y _ novel =>
      cases List.mem_singleton.mp x
      cases List.mem_singleton.mp y
      exact (novel (.refl _)).elim
  · rintro (rfl|⟨rev,cert,improved,rfl⟩)
    · exact GeneralDictionaryCompoundStep238.step
    · exact ⟨root,.root,.administrative (.reobserve root rev cert improved)⟩

end Yulang.GeneralMixedCompoundSourcePrefix308
