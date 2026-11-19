import Yulang.GeneralRebaseProjectionSettle266

namespace Yulang.GeneralRebaseWeakLift266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseProjectedBudget264 (Trace)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseProjectionObserver266 (Witness observe step_exact)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

theorem append {owners : List Nat} {pool : List Output}
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first middle last : SourceState roles} {m n : Nat}
 (prior : Trace owners pool registry root m first middle)
 (suffix : Trace owners pool registry root n middle last) :
 Trace owners pool registry root (m+n) first last := by
 induction suffix with
 | refl state => exact prior
 | stutter _ step same ih => exact .stutter (ih prior) step same
 | advance _ step changed ih => exact .advance (ih prior) step changed

def WeakLiftable (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : SourceState roles) : Prop :=
 ∀ (source : SourceState roles) (last : State (Basis owners pool)),
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) start source →
 Witness owners pool registry root (project owners pool source) last →
 last ≠ project owners pool source →
 ∃ target, Trace owners pool registry root 1 source target ∧ project owners pool target = last

theorem strong_implies_weak (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {start : SourceState roles}
 (lift : GeneralRebaseProjectionLift266.Liftable owners pool registry root start) :
 WeakLiftable owners pool registry root start := by
 intro source last reachable witnessed different
 obtain ⟨target,step,projected⟩ := lift source last reachable witnessed different
 exact ⟨target,.advance (.refl _) step (fun same => different (by rw [←projected]; exact same)),projected⟩

theorem replay (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {start : SourceState roles} {first last : State (Basis owners pool)} {n : Nat}
 (localLift : WeakLiftable owners pool registry root start)
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
   obtain ⟨next,suffix,nextProject⟩ :=
     localLift current middle (GeneralRebaseProjectedBudget264.to_steps prior)
       (equal.symm ▸ exactStep.1) (equal.symm ▸ exactStep.2)
   obtain ⟨final,lifted,result⟩ := ih next (count+1) (append prior suffix) nextProject
   refine ⟨final,?_,result⟩
   have same : count+1+length = count+(length+1) := by omega
   exact same ▸ lifted

/-- Once that observer has no strict edge left, every real source suffix from
a representative of its result leaves the projection unchanged. -/
theorem terminal_path_constant (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles} {terminal : State (Basis owners pool)}
 (stopped : ∀ after, Witness owners pool registry root terminal after → after = terminal)
 (starts : project owners pool first = terminal)
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last) :
 project owners pool last = terminal := by
 induction path with
 | refl => exact starts
 | @tail before after _ step ih => exact stopped _ ⟨before,after,step,ih,rfl⟩

end Yulang.GeneralRebaseWeakLift266
