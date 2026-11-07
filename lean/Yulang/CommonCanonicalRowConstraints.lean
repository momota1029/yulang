import Yulang.CommonCanonicalShapes
import Yulang.CommonBoundCoalescing

/-!
# Row constraints observed by ordinary Common interface types

The row intersection below describes the meaning of an ordinary union of
arrows. It is not an added row-syntax constructor. This module isolates the
type-level mechanism needed to encode finite signed-row constraints in
unrestricted instance families. No decision procedure or undecidability
claim follows from this mechanism alone.
-/

namespace Yulang.CommonCanonicalRowConstraints

open CommonFinite (ProbeAt ProbeStep MaskedProbeStep)

def meetRow (first last : Common.Row) : Common.Row :=
  fun occurrence => first occurrence ∧ last occurrence

/-- Negative input-row positions make a union of arrows observe a row
intersection, with arbitrary types and arbitrary rows. -/
theorem arrow_union_input_rows (input output : Common.Ty) (first last outgoing : Common.Row) :
    Common.Equivalent
      (.union (Common.arrow input first output outgoing) (Common.arrow input last output outgoing))
      (Common.arrow input (meetRow first last) output outgoing) := by
  have rowLeMeet (row first last : Common.Row) :
      Common.rowLe row (meetRow first last) ↔ Common.rowLe row first ∧ Common.rowLe row last := by
    constructor
    · intro below
      exact ⟨fun occurrence member => (below occurrence member).1,
        fun occurrence member => (below occurrence member).2⟩
    · rintro ⟨before, after⟩ occurrence member
      exact ⟨before occurrence member, after occurrence member⟩
  apply (CommonCanonicalShapes.equivalent_iff_probes _ _).mpr
  intro depth rank environment observation
  cases depth <;> cases rank <;> cases observation <;>
    simp [Common.arrow, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep, rowLeMeet]

def lock (type : Common.Ty) : Common.Ty :=
  Common.arrow type Common.rowEmpty type Common.rowEmpty

/-- Sharing an arbitrary type in both polarities turns ordinary subtype
comparison into its existing demand equivalence. -/
theorem lock_subtype_iff (first last : Common.Ty) :
    Common.Subtype (lock first) (lock last) ↔ Common.Equivalent first last := by
  have compare := Common.common_arrow_iff first last first last
    Common.rowEmpty Common.rowEmpty Common.rowEmpty Common.rowEmpty
  simp only [Common.model] at compare
  unfold lock
  rw [compare]
  simp only [Common.rowLe_refl, true_and, and_true, Common.Equivalent]
  exact and_comm

def rowType (row : Common.Row) : Common.Ty :=
  Common.arrow (.base .unit) row (.base .unit) Common.rowEmpty

/-- Row equality is tested by ordinary subtype comparison of a type whose
input and output share the same row-dependent arrow. -/
theorem locked_rows_subtype_iff (first last : Common.Row) :
    Common.Subtype (lock (rowType first)) (lock (rowType last)) ↔ first = last := by
  rw [lock_subtype_iff]
  have before := Common.common_arrow_iff (.base .unit) (.base .unit) (.base .unit) (.base .unit)
    first last Common.rowEmpty Common.rowEmpty
  have after := Common.common_arrow_iff (.base .unit) (.base .unit) (.base .unit) (.base .unit)
    last first Common.rowEmpty Common.rowEmpty
  simp only [Common.model] at before after
  simp only [Common.Equivalent, rowType, before, after, Common.subtype_refl,
    Common.rowLe_refl, true_and, and_true]
  exact ⟨fun both => Common.rowLe_antisymm both.2 both.1,
    fun same => same ▸ ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩⟩

/-- Equality of the full upward instance families detects an unrestricted
existential assignment. The parameter carrier may have any cardinality,
including zero; no residual constraint is imposed on its elements. -/
theorem family_equality_iff_satisfiable {Parameters : Type} (fixed : Common.Ty)
    (values : Parameters → Common.Ty) :
    (∀ target, Common.Subtype fixed target ↔
      ∃ parameters, Common.Subtype (.union fixed (values parameters)) target) ↔
    ∃ parameters, Common.Subtype (values parameters) fixed := by
  constructor
  · intro same
    obtain ⟨parameters, below⟩ := (same fixed).mp (Common.subtype_refl fixed)
    exact ⟨parameters, ((Common.common_union_is_join _ _ _).mp below).2⟩
  · rintro ⟨parameters, below⟩ target
    constructor
    · intro upper
      exact ⟨parameters, (Common.common_union_is_join _ _ _).mpr
        ⟨upper, Common.subtype_trans below upper⟩⟩
    · rintro ⟨parameters, upper⟩
      exact ((Common.common_union_is_join _ _ _).mp upper).1

end Yulang.CommonCanonicalRowConstraints
