import Yulang.GeneralLadderCompiledMinimal306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLadderCompiledRun306
open GeneralDeferredLadderControl304 (Control view remaining)
open GeneralLadderCompiledMinimal306 (compile raw_edges countdown_edges)
open GeneralLadderCompiledPresentation306 (Reach all_levels)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderRefresh301 (before)
open GeneralObservedLadderJournalCompiler301 (table)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralFiniteColoredQuotient306 (QuotientGraph fast_exact projection_sound quotient_closed)

def trace (graph : QuotientGraph Control) : Nat → Control → List Control
  | 0, _ => []
  | k+1, r =>
      match graph.edges r with
      | [] => []
      | x::_ => x :: trace graph k x

inductive Follows (n : Nat) : State roles → List Control → State roles → Prop
  | stop : Follows n s [] s
  | next : RawStep s t → (compile n).project (view n t) = some a →
      Follows n t rest u → Follows n s (a::rest) u

theorem representative {n : Nat} {s : State roles} {r : Control} (h : (compile n).project (view n s) = some r) :
    r ∈ (compile n).representatives := by
  unfold compile at h ⊢
  rw [fast_exact] at h ⊢
  exact (projection_sound h).1

theorem projected_terminal {n : Nat} {s : State roles} {r : Control} (live : Reach n s)
    (h : (compile n).project (view n s) = some r) (zero : remaining n r = 0) :
    ∀ t, ¬ RawStep s t := by
  intro t e
  have nextLive := (GeneralLadderCompiledPresentation306.present n).keepRaw s t live e
  obtain ⟨u,found⟩ := GeneralFiniteRawPresentation306.base_total
    (GeneralLadderCompiledPresentation306.present n) nextLive
  have edge := (raw_edges n live h).mpr ⟨t,e,found⟩
  have bad := (countdown_edges n (representative h) (representative found)).mp edge
  omega

theorem nonempty_quotient {n : Nat} {r : Control} (atRep : r ∈ (compile n).representatives)
    (progress : 0 < remaining n r) : ∃ a ∈ (compile n).edges r, True := by
  unfold compile at atRep ⊢
  rw [fast_exact] at atRep ⊢
  have inside := GeneralFiniteColoredQuotient306.in_domain atRep
  obtain ⟨successor,edge,_⟩ := (GeneralLadderCompiledPresentation306.possible n r inside).mpr progress
  obtain ⟨pin,done⟩ := GeneralFiniteColoredQuotient306.projection_total (observe := fun _ => ())
    (GeneralLadderCompiledPresentation306.closure n)
    (GeneralLadderCompiledPresentation306.closure n r inside successor edge)
  have req := GeneralFiniteColoredQuotient306.representative_fixed
    (GeneralLadderCompiledPresentation306.closure n) atRep
  exact ⟨pin,(GeneralFiniteColoredQuotient306.exact_edges
    (GeneralLadderCompiledPresentation306.closure n) inside req).mpr ⟨successor,edge,done⟩,trivial⟩

theorem run_exact (n budget : Nat) {s : State roles} {r : Control} {len : Nat}
    (path : Counted len (before n) s) (chosen : (compile n).project (view n s) = some r)
    (cost : remaining n r = budget) :
    ∃ t, Follows n s (trace (compile n) budget r) t ∧
      (trace (compile n) budget r).length = budget ∧ Counted (len+budget) (before n) t ∧
      (∀ next, ¬ RawStep t next) := by
  induction budget generalizing s r len with
  | zero => exact ⟨s,.stop,rfl,path,projected_terminal ⟨len,path⟩ chosen cost⟩
  | succ k ih =>
    have positive : 0 < remaining n r := by omega
    obtain ⟨a,used,_⟩ := nonempty_quotient (representative chosen) positive
    cases remainingEdges : (compile n).edges r with
    | nil => rw [remainingEdges] at used; cases used
    | cons x xs =>
      have first : x ∈ (compile n).edges r := remainingEdges.symm ▸ List.mem_cons_self ..
      obtain ⟨mid,move,code⟩ := (raw_edges n ⟨len,path⟩ chosen).mp first
      have decrease := (countdown_edges n (representative chosen) (representative code)).mp first
      have eq : remaining n x = k := by omega
      obtain ⟨t,rest,size,count,noNext⟩ := ih (Counted.tail path move) code eq
      have exactTrace : trace (compile n) (k+1) r = x :: trace (compile n) k x := by
        simp only [trace]
        rw [remainingEdges]
      refine ⟨t,exactTrace.symm ▸ (Follows.next move code rest),?_,?_,noNext⟩
      · rw [exactTrace,List.length_cons,size]
      · simpa only [Nat.add_assoc,Nat.add_comm 1 k] using count

theorem compiled_terminal (n : Nat) {s : State roles} {len : Nat}
    (path : Counted len (before n) s) (r : Control) (chosen : (compile n).project (view n s) = some r) :
    ∃ t, Follows n s (trace (compile n) (remaining n r) r) t ∧
      len + remaining n r = n+2 ∧
      (∀ fuel, GeneralGeneratedDictionaryRun299.run (table t) fuel 0 =
        if n+1 < fuel then some (dictionary (n+1)) else none) ∧
      ∀ m, Models t m → (boundary roles).Evidence registry t m displayRoot (dictionary (n+1)) := by
  obtain ⟨t,run,_,count,halt⟩ := run_exact n (remaining n r) path chosen rfl
  exact ⟨t,run,GeneralDeferredLadderClosed304.halted_outcome n count halt⟩

end Yulang.GeneralLadderCompiledRun306
