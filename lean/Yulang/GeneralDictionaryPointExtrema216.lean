import Yulang.GeneralDictionaryMergeCompletion216

/-! Nonempty point captures have the same computed extrema, independently of
multiplicity/order. Pointness is explicit and is not inferred from Fits alone. -/
namespace Yulang.GeneralDictionaryPointExtrema216
open GeneralNominalAllocation GeneralNominalCaptureMerges CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Interval)

def Points (model : Assignment) (bounds : List Interval) (value : Ty) : Prop :=
  ∀ pair ∈ bounds, Equivalent (model pair.1).1 value ∧ Equivalent (model pair.2).1 value

theorem lower_point (model : Assignment) (bounds : List Interval) (value : Ty)
    (nonempty : bounds ≠ []) (point : Points model bounds value) :
    Equivalent ((lower bounds).eval CommonNominalFullCarrier.model model) value := by
  obtain ⟨pair,member⟩ := List.exists_mem_of_ne_nil bounds nonempty
  exact ⟨(lower_exact model bounds nonempty value).mpr (fun pair member => (point pair member).1.1),
    subtype_trans (point pair member).1.2
      ((lower_exact model bounds nonempty _).mp (subtype_refl _) pair member)⟩

theorem upper_point (model : Assignment) (bounds : List Interval) (value : Ty)
    (nonempty : bounds ≠ []) (point : Points model bounds value) :
    Equivalent ((upper bounds).eval CommonNominalFullCarrier.model model) value := by
  obtain ⟨pair,member⟩ := List.exists_mem_of_ne_nil bounds nonempty
  exact ⟨subtype_trans ((upper_exact model bounds nonempty _).mp (subtype_refl _) pair member)
      (point pair member).2.1,
    (upper_exact model bounds nonempty value).mpr (fun pair member => (point pair member).2.2)⟩

theorem extrema_same (model : Assignment) (first last : List Interval) (value : Ty)
    (firstNonempty : first ≠ []) (lastNonempty : last ≠ [])
    (firstPoint : Points model first value) (lastPoint : Points model last value) :
    Equivalent ((lower first).eval CommonNominalFullCarrier.model model)
      ((lower last).eval CommonNominalFullCarrier.model model) ∧
    Equivalent ((upper first).eval CommonNominalFullCarrier.model model)
      ((upper last).eval CommonNominalFullCarrier.model model) := by
  have a := lower_point model first value firstNonempty firstPoint
  have b := lower_point model last value lastNonempty lastPoint
  have c := upper_point model first value firstNonempty firstPoint
  have d := upper_point model last value lastNonempty lastPoint
  exact ⟨⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩,
    ⟨subtype_trans c.1 d.2,subtype_trans d.1 c.2⟩⟩

end Yulang.GeneralDictionaryPointExtrema216
