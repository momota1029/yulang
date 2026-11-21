import Yulang.GeneralMixedCompoundPointAcc307
import Yulang.GeneralMixedCompoundTailPresentation307
import Yulang.GeneralMixedCompoundTailFan307
import Yulang.GeneralMixedCompoundPointEvidence307

namespace Yulang.Cycle307Smoke
open GeneralMixedCompoundPointExact307 (RawRun exact_lengths_to_verified_halt)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundTailPresentation307 (targets)
open GeneralMixedCompoundTailFan307 (tail injective)

example : targets false = [true] ∧ targets true = [] := by decide
example : RawRun 1 upperState := (exact_lengths_to_verified_halt 1).mpr (Or.inl rfl)
example : RawRun 2 upperState := (exact_lengths_to_verified_halt 2).mpr (Or.inr (Or.inl rfl))
example : RawRun 3 upperState := (exact_lengths_to_verified_halt 3).mpr (Or.inr (Or.inr rfl))
example : ¬ RawRun 4 upperState := fun h => by
  have limit := GeneralMixedCompoundPointExact307.arbitrary_raw_bound h
  omega
example : tail 0 ≠ tail 8 := fun h => (by decide : (0 : Nat) ≠ 8) (injective h)
end Yulang.Cycle307Smoke
