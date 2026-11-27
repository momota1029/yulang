import Yulang.GeneralDeclarativeI65I74FiniteSourceShell461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturedSubpattern462
open GeneralDeclarationPatterns
open Roles (argsSize argsOccurrences)

inductive Edge where
  | argument (index : Nat)
  | fieldValue
  | tagValue

def select : Pattern → Edge → Option Pattern
  | .app _ as, .argument i => as[i]?
  | .record _ p _, .fieldValue => some p
  | .variant _ p, .tagValue => some p
  | _, _ => none

inductive Child : Pattern → Edge → Pattern → Prop where
  | argument : as[i]? = some p → Child (.app key as) (.argument i) p
  | fieldValue : Child (.record label value tail) .fieldValue value
  | tagValue : Child (.variant tag value) .tagValue value

theorem exact_syntactic_child_read {p q : Pattern} {addr : Edge} :
    select p addr = some q ↔ Child p addr q := by
  constructor
  · intro read
    cases p <;> cases addr <;> simp [select] at read
    · exact .argument read
    · subst q; exact .fieldValue
    · subst q; exact .tagValue
  · intro yes
    cases yes with
    | argument found => exact found
    | fieldValue => rfl
    | tagValue => rfl

inductive Subtree : Pattern → List Edge → Pattern → Prop where
  | stop : Subtree p [] p
  | next : Child p a q → Subtree q rest child → Subtree p (a::rest) child

def readSubtree (p : Pattern) : List Edge → Option Pattern
  | [] => some p
  | e::rest => do readSubtree (← select p e) rest

theorem structural_subtree_exact_finite_address {p q : Pattern} {path : List Edge} :
    readSubtree p path = some q ↔ Subtree p path q := by
  induction path generalizing p with
  | nil =>
    constructor
    · intro yes
      cases (Option.some.inj yes)
      exact .stop
    · intro actual
      cases actual
      rfl
  | cons edge rest ih =>
    constructor
    · intro yes
      change ((select p edge).bind fun child => readSubtree child rest) = some q at yes
      obtain ⟨child,found,next⟩ := Option.bind_eq_some_iff.mp yes
      exact .next (exact_syntactic_child_read.mp found) (ih.mp next)
    · intro exact
      cases exact with
      | next sel more =>
        simp [readSubtree,exact_syntactic_child_read.mpr sel,ih.mpr more,Option.bind]

def captured (cap : Nat → Pattern) (p : Pattern) : Roles.Term :=
  (normalize (p.subst cap)).encode

private theorem args_include_same_captured_term (cap : Nat → Pattern)
    {as : List Pattern} {i : Nat} {p : Pattern} (found : as[i]? = some p) :
    (encodeArgs (normalizeArgs (substArgs cap as)))[i]? = some (captured cap p) := by
  induction as generalizing i with
  | nil => cases i <;> simp at found
  | cons h t ih =>
    cases i with
    | zero =>
      have same : h = p := Option.some.inj found
      subst p
      rfl
    | succ i => exact ih found

private theorem checked_member_counts {ts : List Roles.Term} {i : Nat} {t : Roles.Term}
    (same : ts[i]? = some t) :
    t.size ≤ argsSize ts ∧ ∀ n, t.occurrences n ≤ argsOccurrences n ts := by
  induction ts generalizing i with
  | nil => cases i <;> simp at same
  | cons h tail ih =>
    cases i with
    | zero =>
      have eq : h = t := Option.some.inj same
      subst h
      exact ⟨Nat.le_add_right ..,fun _ => Nat.le_add_right ..⟩
    | succ i =>
      obtain ⟨sizes,counts⟩ := ih same
      refine ⟨?_,fun n => ?_⟩
      · change _ ≤ h.size + argsSize tail
        omega
      · have c := counts n
        change _ ≤ h.occurrences n + argsOccurrences n tail
        omega

theorem each_retained_child_preserves_captured_counts_and_strict_size
    {p q : Pattern} {e : Edge} (found : Child p e q) (cap : Nat → Pattern) :
    (captured cap q).size < (captured cap p).size ∧
      ∀ n, (captured cap q).occurrences n ≤ (captured cap p).occurrences n := by
  cases found with
  | argument actual =>
    have ⟨sizes,counts⟩ := checked_member_counts (args_include_same_captured_term cap actual)
    refine ⟨?_,counts⟩
    change _ < 1 + argsSize (encodeArgs (normalizeArgs (substArgs cap _)))
    omega
  | fieldValue =>
    refine ⟨?_,fun n => ?_⟩
    · simp only [captured,Pattern.subst,normalize,Pattern.encode,Roles.Term.size,argsSize]
      omega
    · simp only [captured,Pattern.subst,normalize,Pattern.encode,Roles.Term.occurrences,argsOccurrences]
      omega
  | tagValue =>
    refine ⟨?_,fun n => ?_⟩
    · simp only [captured,Pattern.subst,normalize,Pattern.encode,Roles.Term.size,argsSize]
      omega
    · simp only [captured,Pattern.subst,normalize,Pattern.encode,Roles.Term.occurrences,argsOccurrences]
      omega

theorem every_retained_subtree_preserves_captured_counts_with_exact_depth_slack
    {p q : Pattern} {path : List Edge} (shape : Subtree p path q) (cap : Nat → Pattern) :
    (captured cap q).size + path.length ≤ (captured cap p).size ∧
      ∀ n, (captured cap q).occurrences n ≤ (captured cap p).occurrences n := by
  induction shape with
  | stop => simp
  | next one rest ih =>
    obtain ⟨s,c⟩ := each_retained_child_preserves_captured_counts_and_strict_size one cap
    obtain ⟨ss,cs⟩ := ih
    refine ⟨?_,fun n => Nat.le_trans (cs n) (c n)⟩
    simp only [List.length_cons]
    omega

theorem nonempty_actual_subtree_is_stable_under_every_capture
    {p q : Pattern} {path : List Edge} (shape : Subtree p path q) (strict : path ≠ []) :
    StableSmaller [p] [q] := by
  intro cap
  obtain ⟨s,c⟩ := every_retained_subtree_preserves_captured_counts_with_exact_depth_slack shape cap
  have pos : 0 < path.length := List.length_pos_iff.mpr strict
  refine ⟨?_,?_⟩
  · change (captured cap q).size + 0 < (captured cap p).size + 0
    omega
  · intro n
    change (captured cap q).occurrences n + 0 ≤ (captured cap p).occurrences n + 0
    simpa only [Nat.add_zero] using c n

def StrictOriginalSubtree (head child : List Pattern) (path : List Edge) : Prop :=
  ∃ p q, head = [p] ∧ child = [q] ∧ path ≠ [] ∧ Subtree p path q

def checkStrictSubtree (head child : List Pattern) (path : List Edge) : Bool :=
  match head,child with
  | [p],[q] => !path.isEmpty && decide (readSubtree p path = some q)
  | _,_ => false

theorem check_strict_subtree_iff_independent_original_scope (head child : List Pattern)
    (path : List Edge) : checkStrictSubtree head child path = true ↔ StrictOriginalSubtree head child path := by
  unfold checkStrictSubtree
  split
  · rename_i p q
    constructor
    · intro yes
      have both := (Bool.and_eq_true ..).mp yes
      have source : path ≠ [] := by
        intro gone
        subst path
        cases both.1
      exact ⟨p,q,rfl,rfl,source,structural_subtree_exact_finite_address.mp (of_decide_eq_true both.2)⟩
    · rintro ⟨p',q',eqP,eqQ,notEmpty,chosen⟩
      have ep := List.singleton_inj.mp eqP
      have eq := List.singleton_inj.mp eqQ
      subst p' q'
      apply (Bool.and_eq_true ..).mpr
      refine ⟨?_,decide_eq_true (structural_subtree_exact_finite_address.mpr chosen)⟩
      cases path with
      | nil => exact (notEmpty rfl).elim
      | cons => rfl
  · rename_i missing
    constructor
    · intro failed
      cases failed
    · rintro ⟨p,q,h,c,_⟩
      exact (missing p q h c).elim

theorem actual_indexed_head_subtree_supplies_exact_clause_stability
    {p : Checker408.Problem} (a : WrittenPattern460.OriginalAnchor p) {path : List Edge}
    (yes : checkStrictSubtree a.declaration.head a.clause.arguments path = true) :
    StableSmaller a.declaration.head a.clause.arguments := by
  obtain ⟨head,child,h,c,strict,keeps⟩ := (check_strict_subtree_iff_independent_original_scope ..).mp yes
  rw [h,c]
  exact nonempty_actual_subtree_is_stable_under_every_capture keeps strict

end Yulang.GeneralDeclarativeI65.I72.CapturedSubpattern462
