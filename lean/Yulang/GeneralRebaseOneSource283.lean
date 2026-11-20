import Yulang.GeneralRebaseSliceEvidence283
import Yulang.GeneralRebaseLoopConstant282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseOneSource283
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent model subtype_refl)
open GeneralRebaseLoopBase282 (union_same inter_same equiv_trans)
open GeneralPresenceUsedSupport245 (typedReads)

inductive One : TyTerm Nat → Nat → Prop
  | var (n : Nat) : One (.var n) n
  | join : One a n → One b n → One (.union a b) n
  | meet : One a n → One b n → One (.inter a b) n

def one : TyTerm Nat → Option Nat
  | .var n => some n
  | .union a b | .inter a b => do
    let x ← one a
    let y ← one b
    if x = y then some x else none
  | _ => none

theorem accepts {term : TyTerm Nat} {n : Nat} (valid : One term n) : one term = some n := by
  induction valid <;> simp_all [one]

theorem reflects (term : TyTerm Nat) (n : Nat) (result : one term = some n) : One term n := by
  induction term generalizing n <;> simp only [one,Option.bind_eq_bind] at result
  case var v =>
    have same : v = n := Option.some.inj result
    subst n
    exact .var v
  case union a b ihA ihB =>
    cases eqA : one a with
    | none => simp [eqA] at result
    | some x =>
      cases eqB : one b with
      | none => simp [eqA,eqB] at result
      | some y =>
        by_cases h : x = y
        · have key : x = n := by simpa [eqA,eqB,h] using result
          subst y; subst n
          exact .join (ihA x eqA) (ihB x eqB)
        · simp [eqA,eqB,h] at result
  case inter a b ihA ihB =>
    cases eqA : one a with
    | none => simp [eqA] at result
    | some x =>
      cases eqB : one b with
      | none => simp [eqA,eqB] at result
      | some y =>
        by_cases h : x = y
        · have key : x = n := by simpa [eqA,eqB,h] using result
          subst y; subst n
          exact .meet (ihA x eqA) (ihB x eqB)
        · simp [eqA,eqB,h] at result
  all_goals cases result

theorem reads_exact {term : TyTerm Nat} {n : Nat} (valid : One term n) {i : Nat} :
    i ∈ typedReads term ↔ i = n := by
  induction valid <;> simp_all [typedReads]

theorem meaning {term : TyTerm Nat} {n : Nat} (valid : One term n) (m : Assignment) :
    Equivalent (term.eval model m) (m n).1 := by
  induction valid with
  | var => exact ⟨subtype_refl _,subtype_refl _⟩
  | @join a n b left right ihL ihR =>
    change Equivalent (.union (a.eval model m) (b.eval model m)) (m n).1
    exact equiv_trans (GeneralPresenceCommonLaws245.common_laws.union_congr _ _ _ _ ihL ihR) (union_same _)
  | @meet a n b left right ihL ihR =>
    change Equivalent (.inter (a.eval model m) (b.eval model m)) (m n).1
    exact equiv_trans (GeneralPresenceCommonLaws245.common_laws.inter_congr _ _ _ _ ihL ihR) (inter_same _)

end Yulang.GeneralRebaseOneSource283
