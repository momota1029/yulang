import Yulang.GeneralRebaseClosedOriginDriver270
import Yulang.GeneralRebaseAcyclicNominal270

namespace Yulang.GeneralRebaseClosedOriginFixture270
open GeneralRebaseClosedOriginDriver270 (covered inspect inspectRoot inspectRoot_sound totalEdges)
open GeneralNominalVersionedCycles232 (RootCycle Cyclic)

namespace Positive
open GeneralRebaseVariantNominalFixture270 (journal root model full_model)

theorem full_coverage : covered journal = true := by decide +kernel

theorem full_matrix : totalEdges journal = true := by decide +kernel

theorem computed_root : inspectRoot journal root = some true := by decide +kernel

theorem actual_root : RootCycle journal root := by
 have proof := inspectRoot_sound journal ⟨model,full_model⟩ root
 rw [computed_root] at proof
 exact proof

/-- Root does not need to be passed as a list of offsets. A query for
an origin not covered by the representation stays indeterminate. -/
theorem unstored_source_unknown : inspect journal (.source 99) = none := by decide +kernel

end Positive

namespace Negative
open GeneralRebaseAcyclicNominal270 (journal root model full_model)

theorem full_coverage : covered journal = true := by decide +kernel

theorem full_matrix : totalEdges journal = true := by decide +kernel

theorem computed_root : inspectRoot journal root = some false := by decide +kernel

theorem actual_root_absent : ¬ RootCycle journal root := by
 have proof := inspectRoot_sound journal ⟨model,full_model⟩ root
 rw [computed_root] at proof
 exact proof

end Negative
end Yulang.GeneralRebaseClosedOriginFixture270
