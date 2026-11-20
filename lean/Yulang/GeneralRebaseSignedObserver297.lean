import Yulang.GeneralRebaseSourceQuestions297

namespace Yulang.GeneralRebaseSignedObserver297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceObserver267 (Probes installAt)
open GeneralRebaseSourceSelect267 (Guard)
open GeneralRebaseSourceQuestions297 (entries holds questions Question Checked signed of_focus)
open GeneralRebaseSignedModels297 (Sign)
open GeneralRebaseFiniteWitnessTable297 (hit)
open GeneralRebaseLiveProjection264 (project)

def withModels (base : Probes roles) (xs : List Assignment)
    (prior : Assignment → Bool) (test : Plan roles → Assignment → Bool) : Probes roles :=
  { base with
    novelty := fun _ p => hit xs (signed prior test) (p,.reject)
    joint := fun _ p => hit xs (signed prior test) (p,.pass) }

variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
  {root : Occurrence roles} {checked : (Boundary roles).Checked r}
  {base : Probes roles} {xs : List Assignment}
  {prior : Assignment → Bool} {test : Plan roles → Assignment → Bool}

theorem novelty_exact
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (p : Plan roles) (listed : p ∈ entries r s root checked) (focus : Occurrence roles) :
    (withModels base xs prior test).novelty focus p = true ↔
      ¬ GeneralRebaseInstallChecks267.semanticCommitted s p :=
  (GeneralRebaseSourceQuestions297.exact cover cert p listed .reject).trans
    (GeneralRebaseSignedModels297.reject_exact s p)

theorem joint_exact
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (e : Effect roles) (listed : e.plan ∈ entries r s root checked)
    (reg : e.registry = Encoded r) (snap : e.snapshot = s.core) (focus : Occurrence roles) :
    (withModels base xs prior test).joint focus e.plan = true ↔ ∃ m, Residual s e m :=
  (GeneralRebaseSourceQuestions297.exact cover cert e.plan listed .pass).trans
    (exists_congr (GeneralRebaseSignedModels297.pass_exact checked reach reg snap))

theorem sound_guards
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (focus : Occurrence roles) (generated : Generated s.core.erased.current root focus) :
    GeneralRebaseInstallCandidates267.Probes (Encoded r) s
      ((withModels base xs prior test).novelty focus) ((withModels base xs prior test).joint focus)
      (atFocus (Encoded r) s root focus (declChecked checked)) :=
  ⟨fun p listed yes => (novelty_exact cover cert p (of_focus r s root focus checked generated p listed) focus).mp yes,
    fun p listed yes e reg snap eq => by
      subst p
      exact (joint_exact reach cover cert e (of_focus r s root focus checked generated e.plan listed) reg snap focus).mp yes⟩

theorem complete_guards
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (focus : Occurrence roles) (generated : Generated s.core.erased.current root focus) :
    GeneralRebaseInstallCoverage267.Covers (Encoded r) s
      ((withModels base xs prior test).novelty focus) ((withModels base xs prior test).joint focus)
      (atFocus (Encoded r) s root focus (declChecked checked)) :=
  ⟨fun p listed yes => (novelty_exact cover cert p (of_focus r s root focus checked generated p listed) focus).mpr yes,
    fun e listed reg snap yes =>
      (joint_exact reach cover cert e (of_focus r s root focus checked generated e.plan listed) reg snap focus).mpr yes⟩

/-- The independent observer obligations not answered by signed install questions. -/
structure Other (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles) : Prop where
  metadata : Metadata (Encoded r) s.core.erased.current.context
  head : ∀ f, Generated s.core.erased.current root f →
    Honest (probes.head f) (atFocus (Encoded r) s root f (declChecked checked))
  total : ∀ f, Generated s.core.erased.current root f →
    GeneralRebaseCompleteHeadProbe267.Covered (probes.head f) (atFocus (Encoded r) s root f (declChecked checked))
  diagnostics : ∀ f, ∀ p ∈ installAt r s root f checked probes, Guard r s f p.packet.declaration.id
  merge : ∀ first ∈ s.core.sites, ∀ last ∈ s.core.sites,
    probes.mergeInputs first last = true ↔ SameInputs (Models s) first last

theorem contracts
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (other : Other r s root checked (withModels base xs prior test)) :
    GeneralRebaseObserverSound267.Sound r s root checked (withModels base xs prior test) ∧
      GeneralRebaseObserverCoverage267.Covers r s root checked (withModels base xs prior test) :=
  ⟨⟨other.metadata,other.head,sound_guards reach cover cert,other.diagnostics,
      fun f fm last lm => (other.merge f fm last lm).mp⟩,
    ⟨other.head,other.total,complete_guards reach cover cert,
      fun f fm last lm => (other.merge f fm last lm).mpr⟩⟩

theorem strict_exact
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (cover : GeneralRebaseFiniteWitnessTable297.Covers (holds s) (questions (entries r s root checked)) xs)
    (cert : Checked s (entries r s root checked) xs prior test)
    (other : Other r s root checked (withModels base xs prior test))
    (owners : List Nat) (pool : List Output)
    (target : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step
      (GeneralRebaseObserverExact267.observe r root s checked (withModels base xs prior test) owners pool)
      (project owners pool s) target ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      project owners pool after = target ∧ target ≠ project owners pool s :=
  let qs := contracts reach cover cert other
  GeneralRebaseObserverExact267.step_iff r root s checked reach _ qs.1 qs.2 owners pool target

end Yulang.GeneralRebaseSignedObserver297
