import Yulang.SemilinearDecisions

/-!
# Sound inexpensive sufficient checks for semilinear containment

A source line is contained in a target line if its base belongs to the target
and each source period belongs to the target period monoid. Equality of the
finite generator sets is checked first. Both tests can avoid constructing any
automata for common comparisons.

This is deliberately only a sufficient condition. A target union can cover a
source jointly, and offsets can hide gaps in a period monoid. A failed fast
check must therefore fall back to the complete decision procedure; it never
establishes noncontainment.
-/

namespace Yulang.SemilinearFastInclusion

open SemilinearWeights

variable {n : Nat}

theorem span_transfer (source target : List (Weight n))
    (generators : ∀ period ∈ source, Span target period)
    (weight : Weight n) (member : Span source weight) : Span target weight := by
  induction member with
  | nil => exact .nil
  | @cons first rest present tail ih => exact (generators first present).append ih

def checkLine (source target : Linear n) : Bool :=
  if SemilinearNormalization.sameLine source target then true
  else SemilinearDecisions.checkLinear target source.base &&
    source.periods.all (fun period => SemilinearDecisions.checkSpan target.periods period)

theorem checkLine_refl (line : Linear n) : checkLine line line = true := by
  simp [checkLine, SemilinearNormalization.sameLine_refl]

theorem checkLine_sound (source target : Linear n) (checked : checkLine source target = true)
    (weight : Weight n) (member : source.Holds weight) : target.Holds weight := by
  unfold checkLine at checked
  split at checked
  next identical => exact (SemilinearNormalization.sameLine_sound source target identical weight).mp member
  next =>
    have parts : SemilinearDecisions.checkLinear target source.base = true ∧
        source.periods.all (fun period => SemilinearDecisions.checkSpan target.periods period) = true := by
      simpa only [Bool.and_eq_true] using checked
    obtain ⟨offset, offsetSpan, baseEqual⟩ := (SemilinearDecisions.checkLinear_exact _ _).mp parts.1
    have generators : ∀ period ∈ source.periods, Span target.periods period := by
      intro period present
      exact (SemilinearDecisions.checkSpan_exact _ _).mp (List.all_eq_true.mp parts.2 _ present)
    obtain ⟨tail, tailSpan, total⟩ := member
    refine ⟨add offset tail, offsetSpan.append (span_transfer _ _ generators tail tailSpan), ?_⟩
    rw [← add_assoc, baseEqual]
    exact total

def check (source target : Semi n) : Bool :=
  source.all fun first => target.any (checkLine first)

theorem check_sound (source target : Semi n) (checked : check source target = true)
    (weight : Weight n) (member : Meaning source weight) : Meaning target weight := by
  obtain ⟨first, present, fact⟩ := member
  obtain ⟨last, targetPresent, accepted⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked first present)
  exact ⟨last, targetPresent, checkLine_sound first last accepted weight fact⟩

theorem check_refl (semi : Semi n) : check semi semi = true := by
  apply List.all_eq_true.mpr
  intro line present
  exact List.any_eq_true.mpr ⟨line, present, checkLine_refl line⟩

end Yulang.SemilinearFastInclusion
