import Yulang.GeneralRebaseJournalChecks283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseIncrementalGate283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install installCore install_models InstallationModels)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty reachable_legacy_empty)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseInstallCache283 (Valid add forward interpret)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseIncrementalHistory283 (update changes rows)
open GeneralRebaseJournalChecks283 (Checks checks recheck_exact checks_exact)
open GeneralRebaseClassDelta283 (Growth class_install)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalRebaseJournalView243 (compile compile_exact)
open Core.PresenceGeneration (CompTerm)

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
  {reg : Registry} {root : Occurrence roles} {cache : List (Entry Nat)}

def changed (cache : List (Entry Nat)) (effect : Effect roles) : List Nat :=
  (changes cache (add cache effect)).map Prod.fst

theorem unchanged (cache : List (Entry Nat)) (effect : Effect roles) (old : Assignment)
    (n : Nat) (clean : n ∉ changed cache effect) : forward cache effect old n = old n :=
  GeneralPresenceOrderedBlock247.solve_outside CommonNominalFullCarrier.model _ _ _ (fun row listed equal =>
    clean (List.mem_map.mpr ⟨row,listed,equal⟩))

theorem rows_exact (cache : List (Entry Nat)) (effect : Effect roles) (old : Assignment) (n : Nat) :
    (forward cache effect old n).2 = (old n).2 :=
  rows _ _ _ _

noncomputable def catalog (state : State roles) :=
  checks (compile state CompTerm.var)

theorem catalog_exact (old : LegacyEmpty state) (a : Assignment) :
    Checks (catalog state) a ↔ Models state a :=
  (checks_exact _ _).trans (compile_exact state old CompTerm.var a)

theorem rechecked (old : LegacyEmpty state) (c : List (Entry Nat)) (e : Effect roles) (a : Assignment) :
    Checks.recheck (catalog state) (changed c e) a (forward c e a) ↔ Models state (forward c e a) :=
  (recheck_exact _ _ _ _ (fun n => (rows_exact c e a n).symm)
    (fun n h => (unchanged c e a n h).symm)).trans (catalog_exact old _)

def new_requests (state : State roles) (effect prior : Effect roles) (a : Assignment) : Prop :=
  Growth prior.plan a (· ∈ requests state.core prior.plan.packet.site.occurrence)
    (· ∈ requests (installCore state.core effect.plan) prior.plan.packet.site.occurrence)

def Delta (state : State roles) (effect : Effect roles) (a : Assignment) : Prop :=
  GeneralNominalVersionedPlans231.Holds effect.plan a ∧ effect.Holds a ∧
  effect.Live (installCore state.core effect.plan) a ∧
  ∀ prior ∈ state.effects, new_requests state effect prior a

theorem factor_install (old : LegacyEmpty state) (a : Assignment) :
    InstallationModels state effect a ↔ Models state a ∧ Delta state effect a := by
  constructor
  · rintro ⟨base,plan,held,live,_,oldLive⟩
    exact ⟨base,plan,held,live,fun prior listed =>
      ((class_install state.core prior.plan.packet.site.occurrence prior.plan effect.plan a).mp
        (oldLive prior listed)).2⟩
  · rintro ⟨base,plan,held,live,growth⟩
    refine ⟨base,plan,held,live,?_,?_⟩
    · intro prior listed
      rw [old.2] at listed
      cases listed
    · intro prior listed
      exact (class_install state.core prior.plan.packet.site.occurrence prior.plan effect.plan a).mpr
        ⟨(base.2.2 prior listed).2,growth prior listed⟩

def Gate (state : State roles) (effect : Effect roles) (cache : List (Entry Nat)) (old : Assignment) : Prop :=
  Checks.recheck (catalog state) (changed cache effect) old (forward cache effect old) ∧
  Delta state effect (forward cache effect old)

theorem gate_exact (old : LegacyEmpty state) (snap : effect.snapshot = state.core) (a : Assignment) :
    Gate state effect cache a ↔ Models (install state effect) (forward cache effect a) :=
  (and_congr (rechecked old cache effect a) Iff.rfl).trans
    ((factor_install old _).symm.trans (install_models snap).symm)

theorem gate_from_old_model (old : LegacyEmpty state) (known : Models state a) :
    Gate state effect cache a ↔
    (∀ row ∈ catalog state, row.reads.any (changed cache effect).contains = true →
      row.Holds (forward cache effect a)) ∧ Delta state effect (forward cache effect a) := by
  unfold Gate
  refine and_congr ((recheck_exact _ _ _ _ (fun n => (rows_exact cache effect a n).symm)
    (fun n h => (unchanged cache effect a n h).symm)).trans ?_) Iff.rfl
  exact GeneralRebaseJournalChecks283.reuse _ _ (fun n => (rows_exact cache effect a n).symm)
    (fun n h => (unchanged cache effect a n h).symm) ((catalog_exact old _).mpr known)

theorem candidate (valid : Valid cache state) (seen : Reachable reg root state)
    (snap : effect.snapshot = state.core) :
    (∃ base, Gate state effect cache (interpret cache base)) ↔
    ∃ a, InstallationModels state effect a :=
  (exists_congr (fun a => gate_exact (reachable_legacy_empty seen) snap (interpret cache a))).trans
    (GeneralRebaseInstallCache283.candidate valid seen snap)

theorem enabled (valid : Valid cache state) (seen : Reachable reg root state)
    (setup : GeneralRebaseCompiledInstall282.Setup reg state effect) :
    GeneralNominalVersionedMixedKernel234.Installable (GeneralNominalCenteredHeadAllocEncoding.registry reg) state effect ↔
      ∃ base, Gate state effect cache (interpret cache base) := by
  rw [candidate valid seen setup.snapshot_eq]
  exact ⟨fun ready => ready.common,GeneralRebaseCompiledInstall282.add_common setup⟩

end Yulang.GeneralRebaseIncrementalGate283
