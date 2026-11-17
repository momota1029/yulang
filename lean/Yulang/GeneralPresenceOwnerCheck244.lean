import Yulang.GeneralPresenceOwnerRewrite244
/-! Executable diagnostics for a sufficient dependency condition. A false
result is not a language rejection and does not authorize changing selection. -/
namespace Yulang.GeneralPresenceOwnerCheck244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244
variable {Name : Type}

def rankCheck (rank : Name → Nat) (entries : List (Entry Name)) : Bool :=
 entries.all fun entry => (typeSources entry.2).all (fun source => decide (rank source < rank entry.1))

def sameRankCheck (rank : Name → Nat) (entries : List (Entry Name)) : Bool :=
 entries.all fun first => entries.all fun last => decide (rank first.1 = rank last.1)

def disjointCheck [DecidableEq Name] (removed retained : List (Entry Name)) : Bool :=
 removed.all fun old => retained.all fun other => decide (old.1 ≠ other.1)

/-- This checks retained-block rewriting only: Coherent and the removed block's
External condition are separate obligations before full definition projection. -/
def readyCheck [DecidableEq Name] (rank : Name → Nat) (removed retained : List (Entry Name)) : Bool :=
 rankCheck rank removed && rankCheck rank retained && sameRankCheck rank retained && disjointCheck removed retained

theorem rankCheck_exact (rank : Name → Nat) (entries : List (Entry Name)) :
 rankCheck rank entries = true ↔ RankedEntries rank entries := by
 simp [rankCheck,RankedEntries,GeneralFiniteDependencyRewrite244.Below]

theorem sameRankCheck_exact (rank : Name → Nat) (entries : List (Entry Name)) :
 sameRankCheck rank entries = true ↔ ∀ first ∈ entries, ∀ last ∈ entries, rank first.1 = rank last.1 := by
 simp [sameRankCheck]

theorem disjointCheck_exact [DecidableEq Name] (removed retained : List (Entry Name)) :
 disjointCheck removed retained = true ↔ DisjointTargets removed retained := by
 simp [disjointCheck,DisjointTargets]

theorem readyCheck_exact [DecidableEq Name] (rank : Name → Nat) (removed retained : List (Entry Name)) :
 readyCheck rank removed retained = true ↔
 ((RankedEntries rank removed ∧ RankedEntries rank retained) ∧
 (∀ first ∈ retained, ∀ last ∈ retained, rank first.1 = rank last.1)) ∧ DisjointTargets removed retained := by
 simp only [readyCheck,Bool.and_eq_true,rankCheck_exact,sameRankCheck_exact,disjointCheck_exact]

theorem checked_shape [DecidableEq Name] (rank : Name → Nat) (removed retained : List (Entry Name))
 (checked : readyCheck rank removed retained = true) :
 (block retained).map (atomSubst (substitution removed)) = block (transform (substitution removed) retained) :=
 owner_block_shape removed retained ((readyCheck_exact ..).mp checked).2

theorem checked_exact [DecidableEq Name] (rank : Name → Nat) (removed retained : List (Entry Name))
 (checked : readyCheck rank removed retained = true) (model : Model) (assignment : Name → Comp model) :
 PresenceNormalForm.All model assignment (block (transform (substitution removed) retained)) ↔
 PresenceNormalForm.All model (fun name => (substitution removed name).eval model assignment) (block retained) :=
 owner_block_exact removed retained ((readyCheck_exact ..).mp checked).2 model assignment

theorem checked_external [DecidableEq Name] (rank : Name → Nat) (removed retained : List (Entry Name))
 (checked : readyCheck rank removed retained = true) :
 ∀ entry ∈ transform (substitution removed) retained, ∀ source ∈ typeSources entry.2,
 ∀ target ∈ transform (substitution removed) retained, target.1 ≠ source := by
 obtain ⟨⟨⟨one,two⟩,same⟩,_⟩ := (readyCheck_exact ..).mp checked
 exact owner_external removed retained one two same

def removed : List (Entry Nat) := [(2,.var 1)]
def retained : List (Entry Nat) := [(3,.var 2)]

theorem acyclic_check : readyCheck id removed retained = true := by decide

theorem acyclic_rewrite : transform (substitution removed) retained = [(3,.var 1)] := by rfl

theorem two_cycle_fails (rank : Nat → Nat) :
 readyCheck rank [(2,.var 3)] [(3,.var 2)] = false := by
 cases h : readyCheck rank [(2,.var 3)] [(3,.var 2)] with
 | false => rfl
 | true =>
   obtain ⟨⟨⟨one,two⟩,_⟩,_⟩ := (readyCheck_exact ..).mp h
   have a := one (2,.var 3) (by simp) 3 (by simp [typeSources])
   have b := two (3,.var 2) (by simp) 2 (by simp [typeSources])
   exact False.elim (Nat.lt_asymm a b)
end Yulang.GeneralPresenceOwnerCheck244
