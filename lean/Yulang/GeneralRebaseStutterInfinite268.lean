import Yulang.GeneralRebaseWeakTerminal268
import Yulang.GeneralRebasePathQuiescent266

namespace Yulang.GeneralRebaseStutterInfinite268
open GeneralDictionaryVersionLoopSource237 (roles registry root)
open GeneralDictionaryVersionLoopIteration239 (state distinct)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Lull)
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralSourceState (Output)

theorem all_edges_lull {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roleTable}
 (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 (all : ∀ edge ∈ edges path, project owners pool edge.after = project owners pool edge.before) :
 Lull registry root owners pool first last := by
 induction path with
 | nil => exact .refl
 | cons edge tail ih =>
   have firstStep : Lull registry root owners pool edge.before edge.after := .tail .refl
     ⟨edge.actual,all edge List.mem_cons_self⟩
   exact GeneralRebaseWeakTerminal268.append firstStep (ih (fun e he => all e (List.mem_cons_of_mem _ he)))

theorem eventual_lull (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ k, Lull registry root owners pool (state N) (state (N+k)) := by
 obtain ⟨N,stabilizes⟩ := GeneralRebaseRoundProjection265.eventual_rounds owners pool state
   GeneralDictionaryVersionLoopNontermination239.backward_round
 refine ⟨N,fun k => ?_⟩
 induction k with
 | zero => exact .refl
 | succ k ih =>
   let n := N+k
   obtain ⟨path⟩ := GeneralRebasePathQuiescent266.of_round
     (GeneralDictionaryVersionLoopNontermination239.backward_round n)
   have same : project owners pool (state n) = project owners pool (state (n+1)) :=
     (stabilizes n (by omega)).trans (stabilizes (n+1) (by omega)).symm
   exact GeneralRebaseWeakTerminal268.append ih (all_edges_lull owners pool path
     (GeneralRebasePathQuiescent266.all_stutter owners pool path same))

theorem nodup_map_of_injective (fn : α → β) (injective : ∀ {a b}, fn a = fn b → a = b)
 (entries : List α) (unique : entries.Nodup) : (entries.map fn).Nodup := by
 induction entries with
 | nil => exact List.nodup_nil
 | cons first rest ih =>
   obtain ⟨notRepeated,nodup⟩ := List.nodup_cons.mp unique
   apply List.nodup_cons.mpr
   refine ⟨?_,ih nodup⟩
   intro repeated
   obtain ⟨other,member,equal⟩ := List.mem_map.mp repeated
   exact notRepeated (injective equal ▸ member)

/-- Even on an actual checked source recurrence, the finite fact basis
does not bound the set of concrete stutter descendants. -/
theorem no_finite_support (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ support : List (GeneralNominalVersionedJournal232.State roles),
 ¬ (∀ target, Lull registry root owners pool (state N) target → target ∈ support) := by
 obtain ⟨N,paths⟩ := eventual_lull owners pool
 refine ⟨N,fun support covered => ?_⟩
 let sample := (List.range (support.length+1)).map fun k => state (N+k)
 have injective {a b : Nat} (equal : state (N+a) = state (N+b)) : a = b := by
   apply Classical.byContradiction
   intro different
   exact distinct (by omega : N+a ≠ N+b) equal
 have unique : sample.Nodup := nodup_map_of_injective _ injective _ List.nodup_range
 have contained : sample ⊆ support := by
   intro s listed
   obtain ⟨k,_,rfl⟩ := List.mem_map.mp listed
   exact covered _ (paths k)
 have impossible := unique.length_le_of_subset contained
 simp only [sample,List.length_map,List.length_range] at impossible
 omega

end Yulang.GeneralRebaseStutterInfinite268
