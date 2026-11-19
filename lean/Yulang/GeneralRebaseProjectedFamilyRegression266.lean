import Yulang.GeneralRebaseProjectedFamilyMeaning266
import Yulang.GeneralRebaseRecurrence266

namespace Yulang.GeneralRebaseProjectedFamilyRegression266
open GeneralRebaseCertifiedPath266 (Path)
open GeneralRebaseProjectedFamily266 (Route table CommonTarget)
open GeneralRebaseLiveProjection264 (project)
open GeneralSourceState (Output)
open GeneralDictionaryVersionLoopSource237 (registry root)
open GeneralDictionaryVersionLoopIteration239 (state distinct)

abbrev VersionRoute (n : Nat) := Route registry root (state n)

noncomputable def stopped (n : Nat) : VersionRoute n := ⟨state n,.nil _⟩

noncomputable def continued (n : Nat) (path : Path registry root (state n) (state (n+1))) : VersionRoute n :=
 ⟨state (n+1),path⟩

theorem routes_distinct (n : Nat) (path : Path registry root (state n) (state (n+1))) :
 (stopped n).1 ≠ (continued n path).1 :=
 distinct (by omega : n ≠ n+1)

/-- On the genuine source recurrence, the concrete end of an old guard-checked
round is distinct from its beginning, yet for any fixed basis eventually a
zero-round and a one-round certificate have exactly the same finite target.
Both schedulers are checked on the union of these alternative histories. -/
theorem actual_collision (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ n ≥ N, ∃ path : Path registry root (state n) (state (n+1)),
 (stopped n).1 ≠ (continued n path).1 ∧
 CommonTarget owners pool [stopped n,continued n path] (project owners pool (state n)) ∧
 GeneralRebaseSettle259.settle
    (GeneralRebaseCertifiedObserver266.observe owners pool (table [stopped n,continued n path]))
    (project owners pool (state n)) = .ok (project owners pool (state n)) ∧
 GeneralRebaseSettle259.settle
    (GeneralRebasePositiveRules266.observe (GeneralRebaseEdgeRules266.rules owners pool (table [stopped n,continued n path])))
    (project owners pool (state n)) = .ok (project owners pool (state n)) := by
 obtain ⟨N,constant⟩ := GeneralRebaseRoundProjection265.eventual_rounds owners pool state
   GeneralDictionaryVersionLoopNontermination239.backward_round
 refine ⟨N,fun n ge => ?_⟩
 obtain ⟨path⟩ := GeneralRebasePathQuiescent266.of_round (GeneralDictionaryVersionLoopNontermination239.backward_round n)
 have both : CommonTarget owners pool [stopped n,continued n path] (project owners pool (state n)) := by
   intro route listed
   rcases List.mem_cons.mp listed with same | later
   · cases same; rfl
   · cases List.mem_singleton.mp later
     exact (constant (n+1) (Nat.le_trans ge (Nat.le_succ n))).trans (constant n ge).symm
 have nonempty : ∃ route, route ∈ [stopped n,continued n path] := ⟨stopped n,List.mem_cons_self⟩
 exact ⟨path,routes_distinct n path,both,GeneralRebaseProjectedFamily266.settles owners pool _ nonempty both,
   GeneralRebaseProjectedFamilyMeaning266.rules_settle owners pool _ nonempty both⟩

end Yulang.GeneralRebaseProjectedFamilyRegression266
