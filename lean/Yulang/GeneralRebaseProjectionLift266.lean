import Yulang.GeneralRebaseProjectionObserver266

namespace Yulang.GeneralRebaseProjectionLift266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseProjectedBudget264 (Trace)
open GeneralRebaseCompression266 (Basis runs_snoc)
open GeneralRebaseProjectionObserver266 (Witness observe step_exact)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

theorem witnessed_runs (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles} {count : Nat}
 (trace : Trace owners pool registry root count first last) :
 Runs (observe owners pool registry root) count (project owners pool first) (project owners pool last) := by
 induction trace with
 | refl state => exact .nil _
 | stutter _ _ equal ih => simpa only [equal] using ih
 | advance _ step changed ih =>
   exact runs_snoc ih ((step_exact owners pool registry root _ _).mpr ⟨⟨_,_,step,rfl,rfl⟩,changed⟩)

/-- This lifting condition concerns concrete representatives of *reachable*
source states. It is not assumed automatically by the mathematical observer. -/
def Liftable (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : SourceState roles) : Prop :=
 ∀ (source : SourceState roles) (last : State (Basis owners pool)),
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) start source →
 Witness owners pool registry root (project owners pool source) last →
 last ≠ project owners pool source →
 ∃ target, GeneralNominalVersionedMixedKernel234.Step registry root source target ∧
   project owners pool target = last

/-- A complete finite run lifts under an explicitly local, same-representative
condition, which supplies the witnesses in the order actually encountered. -/
theorem replay (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {start : SourceState roles} {first last : State (Basis owners pool)} {n : Nat}
 (localLift : Liftable owners pool registry root start)
 (run : Runs (observe owners pool registry root) n first last) :
 ∀ current count, Trace owners pool registry root count start current →
   project owners pool current = first →
 ∃ final, Trace owners pool registry root (count+n) start final ∧ project owners pool final = last := by
 induction run with
 | nil state =>
   intro current count prior equal
   exact ⟨current,prior,equal⟩
 | @next length first middle last firstStep rest ih =>
   intro current count prior equal
   have exactStep := (step_exact owners pool registry root first middle).mp firstStep
   obtain ⟨next,sourceStep,nextProject⟩ :=
     localLift current middle (GeneralRebaseProjectedBudget264.to_steps prior)
       (equal.symm ▸ exactStep.1) (equal.symm ▸ exactStep.2)
   have changed : project owners pool next ≠ project owners pool current := by
     rw [nextProject,equal]
     exact exactStep.2
   obtain ⟨final,lifted,result⟩ := ih next (count+1) (.advance prior sourceStep changed) nextProject
   refine ⟨final,?_,result⟩
   have same : count+1+length = count+(length+1) := by omega
   exact same ▸ lifted

theorem replay_start (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {start : SourceState roles} {last : State (Basis owners pool)} {n : Nat}
 (localLift : Liftable owners pool registry root start)
 (run : Runs (observe owners pool registry root) n (project owners pool start) last) :
 ∃ final, Trace owners pool registry root n start final ∧ project owners pool final = last := by
 simpa only [Nat.zero_add] using replay owners pool localLift run start 0 (.refl _) rfl

end Yulang.GeneralRebaseProjectionLift266
