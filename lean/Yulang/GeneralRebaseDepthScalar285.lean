import Yulang.GeneralRebaseDepthRefresh285
import Yulang.GeneralRebaseScalarSnapshot271
import Yulang.GeneralRebaseOutputDepthTrace271

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 11500000
namespace Yulang.GeneralRebaseDepthScalar285
open GeneralDictionaryOutputDepth252 (snapshot plan root registry)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseScalarSnapshot271 (enrich promote)

noncomputable abbrev old := installed.core.erased.current.context
noncomputable def target := GeneralRebaseScalarSnapshot271.context old

theorem preserves_known (name : Nat) :
    GeneralNominalState.Known old.state name → GeneralNominalState.Known target.state name := by
  rintro ⟨slot,equal,graph | nominal⟩
  · change snapshot.view.graph slot ≠ .unresolved at graph
    exact (graph rfl).elim
  · exact ⟨slot,equal,Or.inr nominal⟩

noncomputable def refines : GeneralNominalRefinements.Refines old.state target.state where
  base := (GeneralNominalRefinements.refl old.state).base
  heads := (GeneralNominalRefinements.refl old.state).heads
  nominals := (GeneralNominalRefinements.refl old.state).nominals
  ordinary := fun _ held => held
  known := preserves_known
  reserved := fun _ held => held
  allocated := fun _ held => held
  seed := rfl
  constructors := rfl

theorem from_source (m : Assignment) (raw : GeneralNominalState.Models snapshot m) :
    GeneralNominalState.Models target.state m :=
  (GeneralNominalVersionedInstallation231.replay_private_models plan m).mpr
    ((GeneralNominalVersionedPlans231.private_models_iff _ _).mpr
      ⟨raw,(GeneralDictionaryOutputInputs258.inputs m).1⟩)

theorem cache : CacheSound installed target.state := by
  intro observation recorded
  exact ⟨[],[],.source,.source,fun m _ supported =>
    GeneralCanonicalObservations.recorded_sound target.state m
      (from_source m supported.1) recorded⟩

noncomputable def cert : Refresh installed target where
  refines := refines
  interpretation := rfl
  support := fun _ held => held
  constraints := fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩
  cache := cache

theorem previously_unknown (n : Nat) (small : n ≤ 1) :
    ¬ GeneralNominalState.Known old.state n := by
  rintro ⟨slot,loc,head | ⟨d,found⟩⟩
  · change snapshot.view.graph slot ≠ .unresolved at head
    exact head rfl
  · let slot4 : Fin 4 := slot
    have eqn : slot4.val = n := loc
    have found4 : (if slot4 = (2 : Fin 4) then some GeneralDictionaryOutputDepth252.foo else none) = some d := found
    split at found4
    · rename_i eq
      have vv : slot4.val = 2 := congrArg Fin.val eq
      omega
    · cases found4

theorem present (n : Nat) (small : n ≤ 1) :
    n ∈ GeneralNominalState.sources old.state := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨(⟨n,by omega⟩ : Fin 4),rfl⟩

theorem new_zero : GeneralNominalState.Known target.state 0 :=
  ⟨(0 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

theorem new_one : GeneralNominalState.Known target.state 1 :=
  ⟨(1 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

noncomputable def refreshed := GeneralNominalVersionedRefresh232.refresh installed target

theorem actual_silent_refresh : Step registry root installed refreshed :=
  ⟨root,.root,.refresh root target cert 0 (present 0 (by decide))
    (previously_unknown 0 (by decide)) new_zero⟩

theorem fixed_models (m : Assignment) : Models refreshed m ↔ Models installed m :=
  GeneralNominalVersionedMixedObservations233.refresh_models cert

theorem distinct : refreshed ≠ installed := by
  intro eq
  apply previously_unknown 0 (by decide)
  have result : GeneralNominalState.Known refreshed.core.erased.current.context.state 0 := new_zero
  rwa [eq] at result

theorem actual_followup :
    B4Target.Steps (Step registry root) GeneralDictionaryOutputDepth252.initial refreshed :=
  .tail (.tail .refl GeneralDictionaryOutputDepthInstall252.step) actual_silent_refresh

theorem actual_stutters :
    GeneralRebaseOutputDepthTrace271.observe refreshed = GeneralRebaseOutputDepthTrace271.observe installed :=
  (GeneralRebaseOutputDepthTrace271.at_zero installed refreshed
    GeneralRebaseOutputDepthSuccessor271.projected_install actual_silent_refresh).2

theorem post_refresh_deep_not_known (snap : GeneralNominalState.State)
    (observed : CacheSound refreshed snap) :
    ¬ GeneralNominalState.Known snap 3 :=
  GeneralRebaseDepthRefresh285.no_certified_deep_head_of_model refreshed
    ((fixed_models _).mpr GeneralDictionaryOutputDepthInstall252.installed_model) snap observed rfl

theorem separation :
    (∃ next, Step registry root installed next ∧ next ≠ installed) ∧
    (∀ target, ¬ GeneralRebaseStep258.Step
      (GeneralRebaseSourceStepDriver270.propose GeneralRebaseOutputDepthSuccessor271.support)
      (GeneralRebaseOutputDepthTrace271.observe installed) target) :=
  ⟨⟨refreshed,actual_silent_refresh,distinct⟩,GeneralRebaseOutputDepthSuccessor271.no_second_step⟩

end Yulang.GeneralRebaseDepthScalar285
