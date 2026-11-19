import Yulang.GeneralRebasePathCut266

namespace Yulang.GeneralRebaseCertifiedReverse266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (observe)
open GeneralRebaseCertifiedPath266 (Path edges terminal)
open GeneralRebaseCertifiedPathCount266 (strict_count exact_run)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem suffix_of_terminal_run (observer : Observer basis)
 (deterministic : ∀ {first a b}, Step observer first a → Step observer first b → a = b)
 (seen : Runs observer n first current) (reference : Runs observer m first last)
 (quiet : ∀ after, ¬ Step observer last after) :
 ∃ k, m = n+k ∧ Runs observer k current last := by
 induction seen generalizing m with
 | nil _ => exact ⟨m,by simp,reference⟩
 | next head _ ih =>
   cases reference with
   | nil _ => exact False.elim (quiet _ head)
   | next nextHead nextTail =>
     cases deterministic head nextHead
     obtain ⟨k,counts,tail⟩ := ih nextTail
     exact ⟨k,by omega,tail⟩

theorem same_length_endpoint (observer : Observer basis)
 (deterministic : ∀ {first a b}, Step observer first a → Step observer first b → a = b)
 (one : Runs observer n first current) (two : Runs observer n first other) : current = other := by
 induction one with
 | nil _ => cases two; rfl
 | next head _ ih =>
   cases two with
   | next otherHead otherTail =>
     cases deterministic head otherHead
     exact ih otherTail

/-- Reverse replay for a *single* supplied concrete spine. Every finite
abstract execution starting at its projected source is the exact projection
of a prefix of that same spine, with edge ordering preserved and no mixing of
source representatives. -/
theorem replay (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 {current : State (GeneralRebaseCompression266.Basis owners pool)}
 (seen : Runs (observe owners pool (edges path)) n (project owners pool first) current) :
 ∃ mid, ∃ pre : Path registry root first mid, ∃ suf : Path registry root mid last,
 edges pre ++ edges suf = edges path ∧ strict_count owners pool pre = n ∧
 project owners pool mid = current := by
 let table := observe owners pool (edges path)
 have det : ∀ {start a b}, Step table start a → Step table start b → a = b :=
   fun a b => GeneralRebaseCertifiedPathSettle266.deterministic owners pool path a b
 have nativeRun := exact_run owners pool (edges path) path (fun _ h => h)
 obtain ⟨k,counts,_⟩ := suffix_of_terminal_run table det seen nativeRun (terminal owners pool path)
 obtain ⟨mid,pre,suf,ordered,count⟩ := GeneralRebasePathCut266.cut owners pool path n (by omega)
 have replayed := exact_run owners pool (edges path) pre (GeneralRebasePathCut266.prefix_edges ordered)
 rw [count] at replayed
 exact ⟨mid,pre,suf,ordered,count,same_length_endpoint table det replayed seen⟩

theorem run_budget (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 {current : State (GeneralRebaseCompression266.Basis owners pool)}
 (seen : Runs (observe owners pool (edges path)) n (project owners pool first) current) :
 n ≤ strict_count owners pool path := by
 obtain ⟨k,counts,_⟩ := suffix_of_terminal_run (observe owners pool (edges path))
   (fun a b => GeneralRebaseCertifiedPathSettle266.deterministic owners pool path a b)
   seen (exact_run owners pool (edges path) path (fun _ h => h)) (terminal owners pool path)
 omega


theorem replay_iff (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 (current : State (GeneralRebaseCompression266.Basis owners pool)) (n : Nat) :
 Runs (observe owners pool (edges path)) n (project owners pool first) current ↔
 (∃ mid, ∃ pre : Path registry root first mid, ∃ suf : Path registry root mid last,
   edges pre ++ edges suf = edges path ∧ strict_count owners pool pre = n ∧
   project owners pool mid = current) := by
 constructor
 · exact replay owners pool path
 · rintro ⟨mid,pre,suf,ordered,count,same⟩
   have proof := exact_run owners pool (edges path) pre (GeneralRebasePathCut266.prefix_edges ordered)
   simpa only [count,same] using proof

theorem settle_with_exact_budget (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 GeneralRebaseSettle259.settle (observe owners pool (edges path)) (project owners pool first) =
 .ok (project owners pool last) ∧
 (∀ n, Runs (observe owners pool (edges path)) n (project owners pool first) (project owners pool last) ↔
   n = strict_count owners pool path) := by
 have nativeRun := exact_run owners pool (edges path) path (fun _ h => h)
 have quiet := terminal owners pool path
 refine ⟨GeneralRebaseCertifiedPathSettle266.settles owners pool path,fun n => ⟨?_,?_⟩⟩
 · intro run
   obtain ⟨k,counts,remaining⟩ := suffix_of_terminal_run (observe owners pool (edges path))
     (fun a b => GeneralRebaseCertifiedPathSettle266.deterministic owners pool path a b)
     run nativeRun quiet
   cases remaining with
   | nil _ => omega
   | next first _ => exact False.elim (quiet _ first)
 · intro same
   exact same ▸ nativeRun

end Yulang.GeneralRebaseCertifiedReverse266
