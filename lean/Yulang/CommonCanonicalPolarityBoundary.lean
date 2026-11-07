import Yulang.CommonCanonicalPolarity

/-!
# One polarity-normalization pass need not be a fixed point

The shared parameter in `a -> (a & bottom)` initially occurs in both
polarities, so the polarity pass retains it. Constructor/lattice normalization
then removes the result occurrence, leaving `a -> bottom`. A second polarity
pass sees only the negative occurrence and replaces it with top.

Both passes preserve the subtype-instance family by the existing theorem.
This concrete syntactic counterexample shows that `normalize` itself is not
idempotent. It makes no claim about completeness of a later iteration or
about impossibility of a complete public-interface canonical algorithm.
-/

namespace Yulang.CommonCanonicalPolarityBoundary

open CommonCanonicalInterface (Form)
open CommonCanonicalPolarity (normalize)

def unfrozen : Fin 1 → Bool := fun _ => false

def original : Form 1 :=
  .arrow 0 1 (.atom (.var 0)) (.scalar (.inter (.atom (.var 0)) .bottom))

def firstPass : Form 1 :=
  .arrow 0 1 (.atom (.var 0)) (.scalar .bottom)

def secondPass : Form 1 :=
  .arrow 0 1 .top (.scalar .bottom)

theorem first_pass_exact : normalize unfrozen original = firstPass := by decide +kernel

theorem second_pass_exact : normalize unfrozen firstPass = secondPass := by decide +kernel

theorem successive_passes_different : firstPass ≠ secondPass := by decide +kernel

/-- A concrete counterexample to idempotence of the one-pass normalization. -/
theorem normalize_not_idempotent :
    normalize unfrozen (normalize unfrozen original) ≠ normalize unfrozen original := by
  rw [first_pass_exact, second_pass_exact]
  exact Ne.symm successive_passes_different

end Yulang.CommonCanonicalPolarityBoundary
