import Yulang.GeneralDeclarativeI65I74FiniteSourceShell461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.FiniteCaptureBoundary462
open GeneralDeclarationPatterns
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)

abbrev CaptureTable := List (Nat × Pattern)

def readCapture (t : CaptureTable) (v : Nat) : Pattern :=
  ((t.find? fun e => e.1 == v).map Prod.snd).getD (.var v)

def support (head child : List Pattern) : List Nat :=
  variablesArgs head ++ variablesArgs child

def encodeCapture (head child : List Pattern) (sigma : Nat → Pattern) : CaptureTable :=
  (support head child).map fun v => (v,sigma v)

private theorem direct_lookup_of_written_name (ids : List Nat) (sigma : Nat → Pattern)
    (v : Nat) (seen : v ∈ ids) :
    readCapture (ids.map fun n => (n,sigma n)) v = sigma v := by
  induction ids with
  | nil => cases seen
  | cons n rest ih =>
    by_cases same : n = v
    · subst n
      simp [readCapture]
    · have after : v ∈ rest := (List.mem_cons.mp seen).resolve_left (Ne.symm same)
      have cmp : (n == v) = false := by simp [same]
      simpa [readCapture,cmp] using ih after

theorem finite_capture_reifies_both_actual_original_sides
    (head child : List Pattern) (sigma : Nat → Pattern) :
    substArgs (readCapture (encodeCapture head child sigma)) head = substArgs sigma head ∧
    substArgs (readCapture (encodeCapture head child sigma)) child = substArgs sigma child := by
  constructor <;> apply substArgs_congr
  · intro v present
    exact direct_lookup_of_written_name _ _ _ (List.mem_append_left _ present)
  · intro v present
    exact direct_lookup_of_written_name _ _ _ (List.mem_append_right _ present)

def badCapture (head child : List Pattern) (t : CaptureTable) : Bool :=
  !(checkSmaller (substArgs (readCapture t) head) (substArgs (readCapture t) child))

/-- An exact finite certificate of *failure* of all-captures stability.
There is no bound asserted on the size of the individual captured trees,
and this does not furnish a terminating positive decision procedure. -/
theorem no_all_captures_stability_iff_finite_bad_capture (head child : List Pattern) :
    (¬ StableSmaller head child) ↔ ∃ t : CaptureTable, badCapture head child t = true := by
  classical
  constructor
  · intro no
    obtain ⟨sigma,fail⟩ : ∃ sigma : Nat → Pattern, ¬ Smaller (substArgs sigma head) (substArgs sigma child) := by
      apply Classical.byContradiction
      intro denied
      apply no
      intro sigma
      exact Classical.byContradiction (fun fail => denied ⟨sigma,fail⟩)
    have both := finite_capture_reifies_both_actual_original_sides head child sigma
    refine ⟨encodeCapture head child sigma,?_⟩
    unfold badCapture
    rw [both.1,both.2]
    simpa using Bool.eq_false_iff.mpr (mt (checkSmaller_exact ..).mp fail)
  · rintro ⟨t,failed⟩ stable
    have yes := (checkSmaller_exact ..).mpr (stable (readCapture t))
    simp [badCapture,yes] at failed

theorem stability_is_exactly_universal_over_finite_tables (head child : List Pattern) :
    StableSmaller head child ↔ ∀ t : CaptureTable, badCapture head child t = false := by
  classical
  constructor
  · intro stable t
    have yes := (checkSmaller_exact ..).mpr (stable (readCapture t))
    simp [badCapture,yes]
  · intro no
    apply Classical.byContradiction
    intro failure
    obtain ⟨t,yes⟩ := (no_all_captures_stability_iff_finite_bad_capture ..).mp failure
    rw [no t] at yes
    cases yes

theorem actual_shell_readiness_failure_iff_finite_bad_capture {p : Problem} {a : OriginalAnchor p}
    (authored : StartShell p a) :
    (¬ DeclarationReady (authoredRegistry p.state.core.current) a.declaration) ↔
      ∃ t : CaptureTable, badCapture a.declaration.head a.clause.arguments t = true := by
  have independent := actual_shell_ready_iff_same_original_stable_capture authored
  exact (not_congr independent).trans (no_all_captures_stability_iff_finite_bad_capture ..)

end Yulang.GeneralDeclarativeI65.I72.FiniteCaptureBoundary462
