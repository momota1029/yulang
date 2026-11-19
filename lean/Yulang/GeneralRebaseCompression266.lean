import Yulang.GeneralRebaseProjectedBudget264
import Yulang.GeneralRebaseBudget258
import Yulang.GeneralRebaseStutterWitness265

namespace Yulang.GeneralRebaseCompression266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseProjectedBudget264 (Trace)
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralSourceState (Output)

abbrev Basis (owners : List Nat) (pool : List Output) :=
 GeneralRebaseUniversalBasis263.basis owners pool

/-- An allowed observer admits the exact rescan proposal at all genuine
source transitions that change this projection. No algorithm is presumed. -/
def Covers (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (observe : Observer (Basis owners pool)) : Prop :=
 ∀ (before after : SourceState roles),
 GeneralNominalVersionedMixedKernel234.Step registry root before after →
 project owners pool after ≠ project owners pool before →
 liveFacts after ∈ observe (project owners pool before)

/-- The observer need not reproduce the exact ordering or duplicate structure
of liveFacts; one admitted proposal with the same write result suffices. -/
def CoversResult (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (observe : Observer (Basis owners pool)) : Prop :=
 ∀ (before after : SourceState roles),
 GeneralNominalVersionedMixedKernel234.Step registry root before after →
 project owners pool after ≠ project owners pool before →
 ∃ proposal ∈ observe (project owners pool before),
   project owners pool after = write (project owners pool before) proposal

theorem covers_result (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {observe : Observer (Basis owners pool)} (cover : Covers owners pool registry root observe) :
 CoversResult owners pool registry root observe := by
 intro before after step different
 exact ⟨liveFacts after,cover before after step different,
   GeneralRebaseSourceProjection264.step_square owners pool step⟩

theorem project_step (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {before after : SourceState roles} {observe : Observer (Basis owners pool)}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root before after)
 (different : project owners pool after ≠ project owners pool before)
 (admitted : liveFacts after ∈ observe (project owners pool before)) :
 Step observe (project owners pool before) (project owners pool after) :=
 ⟨liveFacts after,admitted,GeneralRebaseSourceProjection264.step_square owners pool step,
   fun same => different (state_ext _ _ same)⟩

theorem runs_snoc {basis : List Fact} {observe : Observer basis}
 {n : Nat} {start mid finish : State basis}
 (run : Runs observe n start mid) (next : Step observe mid finish) :
 Runs observe (n+1) start finish := by
 induction run with
 | nil state => exact .next next (.nil _)
 | next step _ ih => exact .next step (ih next)

/-- Exact step count, including elimination of every source stutter. -/
theorem runs_of_trace (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles} {observe : Observer (Basis owners pool)} {count : Nat}
 (cover : CoversResult owners pool registry root observe)
 (trace : Trace owners pool registry root count first last) :
 Runs observe count (project owners pool first) (project owners pool last) := by
 induction trace with
 | refl state => exact .nil _
 | stutter _ _ equal ih => simpa only [equal] using ih
 | advance _ step changed ih =>
   obtain ⟨proposal,admitted,square⟩ := cover _ _ step changed
   exact runs_snoc ih ⟨proposal,admitted,square,fun same => changed (state_ext _ _ same)⟩

theorem source_runs (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles} {observe : Observer (Basis owners pool)}
 (cover : Covers owners pool registry root observe)
 (source : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last) :
 ∃ count, Trace owners pool registry root count first last ∧
   Runs observe count (project owners pool first) (project owners pool last) ∧
   count + (project owners pool last).remaining.length ≤ (project owners pool first).remaining.length := by
 obtain ⟨count, trace⟩ := GeneralRebaseProjectedBudget264.from_steps owners pool source
 have run := runs_of_trace owners pool (covers_result owners pool cover) trace
 exact ⟨count,trace,run,GeneralRebaseBudget258.budget observe run⟩

end Yulang.GeneralRebaseCompression266
