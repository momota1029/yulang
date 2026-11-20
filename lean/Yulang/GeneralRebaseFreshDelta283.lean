import Yulang.GeneralRebaseAliasTransport283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFreshDelta283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralRebaseDirtyHistory283 (needs select)
open GeneralRebaseIncrementalHistory283 (changes)

def onlyNew (old : List Nat) (full : List (Entry Nat)) :=
  full.filter (fun row => !(old.contains row.1))

def NoBackReads (old : List Nat) (full : List (Entry Nat)) : Prop :=
  ∀ before ∈ full, before.1 ∈ old → ∀ after ∈ full, after.1 ∉ old →
    after.1 ∉ typedReads before.2

theorem only_fresh (old : List Nat) (full : List (Entry Nat)) (seen : List Nat)
    (allFresh : ∀ n ∈ seen, n ∉ old)
    (safeSeen : ∀ before ∈ full, before.1 ∈ old → ∀ n ∈ seen, n ∉ typedReads before.2)
    (noBack : NoBackReads old full) :
    select old full seen = onlyNew old full := by
  induction full generalizing seen with
  | nil => rfl
  | cons h tail ih =>
    have inside := List.mem_cons_self (a := h) (l := tail)
    have extend (e : Entry Nat) (member : e ∈ tail) : e ∈ h :: tail := List.mem_cons_of_mem _ member
    have nb : NoBackReads old tail :=
      fun x one was y two fresh => noBack x (extend x one) was y (extend y two) fresh
    by_cases known : h.1 ∈ old
    · have clean : needs old seen h = false := by
        unfold needs
        have clean : (typedReads h.2).any seen.contains = false := by
          apply List.any_eq_false.mpr
          intro n used
          simpa only [List.contains_eq_mem,decide_eq_true_eq] using
            fun listed => (safeSeen h inside known n listed) used
        simp [known,clean]
      simp only [select,clean,Bool.false_eq_true,ite_false,onlyNew,List.filter_cons,List.contains_eq_mem,
        known,decide_true,Bool.not_true]
      exact ih seen allFresh (fun row member => safeSeen row (extend row member)) nb
    · have clean : needs old seen h = true := by simp [needs,known]
      simp only [select,clean,ite_true,onlyNew,List.filter_cons,List.contains_eq_mem,known,
        decide_false,Bool.not_false]
      refine congrArg (List.cons h) (ih (h.1 :: seen) ?_ ?_ nb)
      · intro n seen
        rcases List.mem_cons.mp seen with rfl|oldSeen
        · exact known
        · exact allFresh n oldSeen
      · intro e present old eRead found
        rcases List.mem_cons.mp found with rfl|prior
        · exact noBack e (extend e present) old h inside known
        · exact safeSeen e (extend e present) old eRead prior

theorem exact_changes (old full : List (Entry Nat)) (safe : NoBackReads (old.map Prod.fst) full) :
    changes old full = onlyNew (old.map Prod.fst) full :=
  only_fresh _ _ [] (by simp) (by simp) safe

theorem member_exact {old full : List (Entry Nat)} (safe : NoBackReads (old.map Prod.fst) full)
    (e : Entry Nat) : e ∈ changes old full ↔ e ∈ full ∧ e.1 ∉ old.map Prod.fst := by
  rw [exact_changes old full safe]
  simp [onlyNew]

end Yulang.GeneralRebaseFreshDelta283
