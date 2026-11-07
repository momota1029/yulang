import Yulang.CommonRoleCanonicalRows
import Yulang.CommonPatternConcreteRecordTypes

/-!
# Canonical subtraction for exact finite Common record spines

Unlike the width-ended record encoding, this component preserves the
`exactEmpty` terminal of a closed source spine. The payload interpretation is
arbitrary Common syntax, including regular graphs. Normalization removes
hidden duplicate fields according to Common's actual first-field rule.

Physical subtraction is not identified with an outer producer mask: a mask
forgets the removed label's absence, whereas the closed residual knows it.
Pending source spines and role candidate selection remain separate work.
-/

namespace Yulang.CommonRoleClosedRecordResidual

open CommonRoleCanonicalRows (Row normalize residual capture lookup)
open CommonPatternConcreteRecordTypes (recordTypeOf)

/-- Canonical first-field normalization preserves every Common observation,
including known absence and arbitrary nested payload observations. -/
theorem normalize_equivalent (type : Payload → Common.Ty) (fields : Row Payload) :
    Common.Equivalent (recordTypeOf type (normalize fields)) (recordTypeOf type fields) := by
  induction fields with
  | nil => exact Common.equivalent_refl _
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [normalize, recordTypeOf]
      have remove := CommonPatternConcreteRecordTypes.insert_filter_exact
        type label payload (normalize rest)
      have filtered : residual [label] (normalize rest) =
          (normalize rest).filter (fun entry => entry.1 != label) := by
        apply List.filter_congr
        intro entry _
        by_cases same : entry.1 = label <;> simp [same]
      rw [filtered]
      exact Common.equivalent_trans remove
        (CommonPatternConcreteRecordTypes.record_congr label
          (Common.equivalent_refl _) ih)

end Yulang.CommonRoleClosedRecordResidual
