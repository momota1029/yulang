import Yulang.GeneralRebaseSymbolicQuestions298

namespace Yulang.GeneralRebaseLocalProgram298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseSourceWitnessProgram297 (Checks Observed Holds questions callbacks)
open GeneralRebaseRawObserver297 (ExactSafety proposals observe)
open GeneralRebaseFiniteWitnessTable297 (Covers)
open GeneralRebaseSourceQuestions297 (entries)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (Proposal write)
open GeneralSourceState (Output)

structure Local (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) where
  models : List Assignment
  checks : Checks roles
  safety : Occurrence roles → Bool
  safety_exact : ExactSafety r s root safety
  covered : Covers (Holds s) (questions r s root checked) models
  observed : Observed s models (entries r s root checked) checks

def emit {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (code : Local r s root checked) : List Proposal :=
  proposals r s root checked (callbacks code.models code.checks) code.safety

def transition {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (code : Local r s root checked) (owners : List Nat) (pool : List Output) :
    GeneralRebaseStep258.Observer (GeneralRebaseCompression266.Basis owners pool) :=
  observe r s root checked code.models code.checks code.safety owners pool

theorem current_code {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (code : Local r s root checked) (owners : List Nat) (pool : List Output) :
    transition code owners pool (project owners pool s) = emit code :=
  GeneralRebaseRawObserver297.observe_at ..

theorem strict_exact {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output) (t) :
    GeneralRebaseStep258.Step (transition code owners pool) (project owners pool s) t ↔
    ∃ after, (Boundary roles).Step r root s after ∧ project owners pool after = t ∧ t ≠ project owners pool s :=
  GeneralRebaseSourceMetadata297.source_strict_exact reached code.safety_exact code.covered code.observed owners pool t

theorem represents {r : Registry} {s t : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output)
    (step : (Boundary roles).Step r root s t) (different : project owners pool t ≠ project owners pool s) :
    ∃ p ∈ emit code, write (project owners pool s) p = project owners pool t :=
  GeneralRebaseRawObserver297.complete reached code.safety_exact code.covered code.observed owners pool t step different

theorem reifies {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (code : Local r s root checked) (owners : List Nat) (pool : List Output)
    (p : Proposal) (present : p ∈ emit code) :
    ∃ t, (Boundary roles).Step r root s t ∧ write (project owners pool s) p = project owners pool t :=
  let ⟨t,action,exactWrite,_⟩ :=
    GeneralRebaseRawObserver297.sound reached (GeneralRebaseSourceMetadata297.reachable_metadata reached)
      code.safety_exact code.covered code.observed owners pool p present
  ⟨t,action,exactWrite⟩

/-- Classical independently named per-state choice, not an executable
certificate synthesizer and not a common pool for the trace. -/
noncomputable def classicalLocal (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) : Local r s root checked :=
  let h := GeneralRebaseWitnessExistence297.finite_statement r s root checked
  let models := Classical.choose h
  let existsCheck := Classical.choose_spec h
  let c := Classical.choose existsCheck
  let facts := Classical.choose_spec existsCheck
  ⟨models,c,fun f => GeneralRebaseWitnessExistence297.flag (GeneralRebaseRawInstallScan297.Known r s f),
    fun _ _ => GeneralRebaseWitnessExistence297.flag_exact _,facts.2.1,facts.2.2⟩

end Yulang.GeneralRebaseLocalProgram298
