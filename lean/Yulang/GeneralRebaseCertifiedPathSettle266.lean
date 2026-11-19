import Yulang.GeneralRebaseCertifiedPath266

namespace Yulang.GeneralRebaseCertifiedPathSettle266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (Edge observe step_exact)
open GeneralRebaseCertifiedPath266
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

/-- A strict later edge cannot start at the projected origin of a strict head:
the rank has already fallen, even if some intervening edges stutter. -/
theorem no_later_origin (owners : List Nat) (pool : List Output)
 (head : Edge registry root) (tail : Path registry root head.after last)
 (later : Edge registry root) (listed : later ∈ edges tail)
 (strict : project owners pool head.after ≠ project owners pool head.before) :
 project owners pool later.before ≠ project owners pool head.before := by
 intro same
 have upper := (rank_bounds owners pool tail later listed).2
 unfold rank at upper
 rw [same] at upper
 exact Nat.not_lt_of_ge upper
   (GeneralRebaseSourceProjection264.strict_decrease owners pool head.actual strict)

theorem edge_unique (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 (a b : Edge registry root) (ha : a ∈ edges path) (hb : b ∈ edges path)
 (same : project owners pool a.before = project owners pool b.before)
 (aStrict : project owners pool a.after ≠ project owners pool a.before)
 (bStrict : project owners pool b.after ≠ project owners pool b.before) :
 project owners pool a.after = project owners pool b.after := by
 induction path with
 | nil => simp [edges] at ha
 | cons head tail ih =>
   rcases List.mem_cons.mp ha with eqA | laterA <;> rcases List.mem_cons.mp hb with eqB | laterB
   · rw [eqA,eqB]
   · subst a
     exact False.elim (no_later_origin owners pool head tail b laterB aStrict same.symm)
   · subst b
     exact False.elim (no_later_origin owners pool head tail a laterA bStrict same)
   · exact ih laterA laterB

theorem deterministic (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) {start after other}
 (a : Step (observe owners pool (edges path)) start after)
 (b : Step (observe owners pool (edges path)) start other) : after = other := by
 obtain ⟨ae,ha,sa,ea,da⟩ := (step_exact owners pool (edges path) _ _).mp a
 obtain ⟨be,hb,sb,eb,db⟩ := (step_exact owners pool (edges path) _ _).mp b
 exact ea.symm.trans ((edge_unique owners pool path ae be ha hb (sa.trans sb.symm)
   (by simpa only [ea,sa] using da) (by simpa only [eb,sb] using db)).trans eb)

theorem terminal_runs_unique (observer : Observer basis)
 (unique : ∀ {start a b}, Step observer start a → Step observer start b → a = b)
 (one : Runs observer n start last) (two : Runs observer m start other)
 (quiet : ∀ after, ¬ Step observer last after)
 (quiet' : ∀ after, ¬ Step observer other after) : last = other := by
 induction one generalizing m with
 | nil state =>
   cases two with
   | nil => rfl
   | next edge _ => exact False.elim (quiet _ edge)
 | next head _ ih =>
   cases two with
   | nil => exact False.elim (quiet' _ head)
   | next head' tail' =>
     cases unique head head'
     exact ih tail' quiet

theorem settles (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 GeneralRebaseSettle259.settle (observe owners pool (edges path)) (project owners pool first) =
 .ok (project owners pool last) := by
 let table := observe owners pool (edges path)
 obtain ⟨target,_,success,run,_,quiet⟩ := GeneralRebaseClosedObserver259.completion table
   (GeneralRebaseCertifiedObserver266.closed owners pool (edges path)) (project owners pool first)
 obtain ⟨_,_,witness⟩ := projected owners pool (edges path) path (fun _ member => member)
 have equal := terminal_runs_unique table (fun a b => deterministic owners pool path a b)
   run witness quiet (terminal owners pool path)
 exact success.trans (congrArg Except.ok equal)

end Yulang.GeneralRebaseCertifiedPathSettle266
