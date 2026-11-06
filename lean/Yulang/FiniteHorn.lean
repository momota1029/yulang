import Yulang.FiniteWorklist

/-!
# Exact finite Horn saturation

A rule adds one fact when every premise is already known. The executable
closure inserts a fresh fact before rescanning the rules. Its internal
capacity is the size of the complete finite fact universe: each recursive
step inserts a distinct fact, so this is a termination argument, not a bound
on derivation depth. Callers supply no fuel.

`Derives` is an independent inductive rule judgement. Saturation computes
exactly that judgement, and therefore preserves every interpretation under
which the rules are valid.
-/

namespace Yulang.FiniteHorn

variable {Fact : Type}

structure Rule (Fact : Type) where
  premises : List Fact
  conclusion : Fact

inductive Derives (rules : List (Rule Fact)) : Fact → Prop where
  | applyRule (rule : Rule Fact) : rule ∈ rules →
      (∀ premise ∈ rule.premises, Derives rules premise) → Derives rules rule.conclusion

def Enabled (rules : List (Rule Fact)) (seen : List Fact) (fact : Fact) : Prop :=
  ∃ rule ∈ rules, rule.conclusion = fact ∧ ∀ premise ∈ rule.premises, premise ∈ seen

def enabled [DecidableEq Fact] (rules : List (Rule Fact)) (seen : List Fact) (fact : Fact) : Bool :=
  rules.any fun rule => decide (rule.conclusion = fact) && rule.premises.all (fun premise => decide (premise ∈ seen))

theorem enabled_exact [DecidableEq Fact] (rules : List (Rule Fact)) (seen : List Fact) (fact : Fact) :
    enabled rules seen fact = true ↔ Enabled rules seen fact := by
  simp only [enabled, Enabled, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]

def firstFresh [DecidableEq Fact] (rules : List (Rule Fact)) (seen : List Fact) :
    List Fact → Option Fact
  | [] => none
  | fact :: rest =>
      if fact ∉ seen ∧ enabled rules seen fact = true then some fact
      else firstFresh rules seen rest

theorem firstFresh_some [DecidableEq Fact] (rules : List (Rule Fact))
    (seen facts : List Fact) {fact : Fact}
    (found : firstFresh rules seen facts = some fact) :
    fact ∈ facts ∧ fact ∉ seen ∧ Enabled rules seen fact := by
  induction facts with
  | nil => cases found
  | cons first rest ih =>
      simp only [firstFresh] at found
      split at found
      · rename_i chosen
        have same : first = fact := Option.some.inj found
        subst fact
        exact ⟨List.mem_cons_self, chosen.1, (enabled_exact rules seen first).mp chosen.2⟩
      · obtain ⟨member, fresh, enabled⟩ := ih found
        exact ⟨List.mem_cons_of_mem _ member, fresh, enabled⟩

theorem firstFresh_none_iff [DecidableEq Fact] (rules : List (Rule Fact))
    (seen facts : List Fact) :
    firstFresh rules seen facts = none ↔
      ∀ fact ∈ facts, Enabled rules seen fact → fact ∈ seen := by
  induction facts with
  | nil => simp [firstFresh]
  | cons first rest ih =>
      simp only [firstFresh]
      split
      · rename_i chosen
        constructor
        · intro impossible
          cases impossible
        · intro closed
          exact False.elim (chosen.1 (closed first List.mem_cons_self
            ((enabled_exact rules seen first).mp chosen.2)))
      · rename_i notChosen
        rw [ih]
        constructor
        · intro closed fact member possible
          rcases List.mem_cons.mp member with rfl | member
          · by_cases present : fact ∈ seen
            · exact present
            · exact False.elim (notChosen ⟨present, (enabled_exact rules seen fact).mpr possible⟩)
          · exact closed fact member possible
        · intro closed fact member possible
          exact closed fact (List.mem_cons_of_mem _ member) possible

def run [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact) :
    Nat → List Fact → List Fact
  | 0, seen => seen
  | capacity + 1, seen =>
      match firstFresh rules seen facts with
      | none => seen
      | some fact => run rules facts capacity (fact :: seen)

def saturate [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact) : List Fact :=
  run rules facts facts.length []

theorem run_nodup [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (capacity : Nat) (seen : List Fact) (distinct : seen.Nodup) :
    (run rules facts capacity seen).Nodup := by
  induction capacity generalizing seen with
  | zero => exact distinct
  | succ capacity ih =>
      simp only [run]
      cases found : firstFresh rules seen facts with
      | none => exact distinct
      | some next =>
          exact ih (next :: seen) (List.nodup_cons.mpr
            ⟨(firstFresh_some rules seen facts found).2.1, distinct⟩)

theorem saturate_nodup [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact) :
    (saturate rules facts).Nodup := run_nodup rules facts facts.length [] (by simp)

theorem saturate_length_le [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (complete : ∀ fact, fact ∈ facts) : (saturate rules facts).length ≤ facts.length :=
  (saturate_nodup rules facts).length_le_of_subset (fun fact _ => complete fact)

theorem run_sound [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (capacity : Nat) (seen : List Fact) (sound : ∀ fact ∈ seen, Derives rules fact) :
    ∀ fact ∈ run rules facts capacity seen, Derives rules fact := by
  induction capacity generalizing seen with
  | zero => exact sound
  | succ capacity ih =>
      simp only [run]
      cases found : firstFresh rules seen facts with
      | none => exact sound
      | some next =>
          obtain ⟨_, _, rule, member, same, premises⟩ := firstFresh_some rules seen facts found
          apply ih
          intro fact member'
          rcases List.mem_cons.mp member' with rfl | old
          · rw [← same]
            exact .applyRule rule member (fun premise present => sound premise (premises premise present))
          · exact sound fact old

theorem run_closed [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (complete : ∀ fact, fact ∈ facts)
    (capacity : Nat) (seen : List Fact) (distinct : seen.Nodup)
    (enough : facts.length ≤ seen.length + capacity) :
    ∀ fact, Enabled rules (run rules facts capacity seen) fact →
      fact ∈ run rules facts capacity seen := by
  induction capacity generalizing seen with
  | zero =>
      intro fact _
      exact FiniteWorklist.saturated facts seen complete distinct (by simpa using enough) fact
  | succ capacity ih =>
      simp only [run]
      cases found : firstFresh rules seen facts with
      | none =>
          intro fact possible
          exact (firstFresh_none_iff rules seen facts).mp found fact (complete fact) possible
      | some next =>
          have fresh := (firstFresh_some rules seen facts found).2.1
          apply ih (next :: seen) (List.nodup_cons.mpr ⟨fresh, distinct⟩)
          simp only [List.length_cons]
          omega

theorem saturate_sound [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact) :
    ∀ fact ∈ saturate rules facts, Derives rules fact :=
  run_sound rules facts facts.length [] (by simp)

theorem saturate_closed [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (complete : ∀ fact, fact ∈ facts) :
    ∀ fact, Enabled rules (saturate rules facts) fact → fact ∈ saturate rules facts :=
  run_closed rules facts complete facts.length [] (by simp) (by simp)

theorem saturate_exact [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (complete : ∀ fact, fact ∈ facts) (fact : Fact) :
    fact ∈ saturate rules facts ↔ Derives rules fact := by
  constructor
  · exact saturate_sound rules facts fact
  · intro derived
    induction derived with
    | applyRule rule member _ ih =>
        exact saturate_closed rules facts complete rule.conclusion ⟨rule, member, rfl, ih⟩

def Valid (holds : Fact → Prop) (rule : Rule Fact) : Prop :=
  (∀ premise ∈ rule.premises, holds premise) → holds rule.conclusion

theorem Derives.sound {rules : List (Rule Fact)} {holds : Fact → Prop}
    (valid : ∀ rule ∈ rules, Valid holds rule) {fact : Fact}
    (derived : Derives rules fact) : holds fact := by
  induction derived with
  | applyRule rule member _ ih => exact valid rule member ih

theorem saturate_preserves [DecidableEq Fact] (rules : List (Rule Fact)) (facts : List Fact)
    (holds : Fact → Prop) (valid : ∀ rule ∈ rules, Valid holds rule) :
    ∀ fact ∈ saturate rules facts, holds fact :=
  fun fact member => (saturate_sound rules facts fact member).sound valid

end Yulang.FiniteHorn
