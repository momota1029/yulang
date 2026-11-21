import Yulang.GeneralDeclarativeRecordPayloads330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordConsumption330
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordPayloads330 (Field all_mode opaque_payload)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeOrderedRecord326 (order exact_order lookup_unique)
open CommonRoleCanonicalRows (Row normalize normalize_unique lookup lookup_normalize)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Subtype)

theorem lookup_iff {raw : Row Expr} : Field key raw e ↔ lookup key raw = some e := by
  constructor
  · intro one
    induction one with
    | here => simp [lookup]
    | later ne _ ih => simpa [lookup,Ne.symm ne] using ih
  · intro hit
    induction raw with
    | nil => cases hit
    | cons hd rest ih =>
      obtain ⟨label,payload⟩ := hd
      by_cases same : label = key
      · subst label
        have agree : payload = e := by simpa [lookup] using hit
        subst payload
        exact .here
      · exact .later same (ih (by simpa [lookup,Ne.symm same] using hit))

theorem read_field {raw : Row Expr} (printed : order (normalize raw) keys = some picked)
    (used : (key,e) ∈ picked) : Field key raw e := by
  have noDuplicates := normalize_unique raw
  obtain ⟨_,listed⟩ := exact_order noDuplicates printed
  apply lookup_iff.mpr
  rw [← lookup_normalize raw]
  exact lookup_unique noDuplicates ((listed _).mp used).1

/-- Use the actual compiler's two ordered field lists directly:
membership at a requested label identifies the same raw occurrence
used by the interval proof. There is no independent Field premise and
there is no claim of a canonical opaque centre/tail. -/
theorem from_ordered_endpoints {s : State} {p : Supported s done} (box : Bounds s arg)
    (low : Spine (restriction p) arg.lower lower endL)
    (high : Spine (restriction p) arg.upper upper endU)
    (left : order (normalize lower) keys = some first)
    (right : order (normalize upper) keys = some last)
    (requested : key ∈ keys) (m : Assignment) (valid : Models s m) :
    ∃ e f payload,
      (key,e) ∈ first ∧ (key,f) ∈ last ∧
      project key false [] (m arg.center).1 = some payload ∧
      Subtype (value (environment m) .actual e) payload ∧
      Subtype payload (value (environment m) .actual f) := by
  obtain ⟨leftLabels,_⟩ := exact_order (normalize_unique lower) left
  obtain ⟨rightLabels,_⟩ := exact_order (normalize_unique upper) right
  obtain ⟨⟨lk,e⟩,leftMember,eqL⟩ := List.mem_map.mp (leftLabels.symm ▸ requested)
  obtain ⟨⟨rk,f⟩,rightMember,eqR⟩ := List.mem_map.mp (rightLabels.symm ▸ requested)
  change lk = key at eqL
  change rk = key at eqR
  subst lk
  subst rk
  obtain ⟨middle,proof⟩ := opaque_payload box low high (read_field left leftMember)
    (read_field right rightMember) m valid
  exact ⟨e,f,middle,leftMember,rightMember,proof⟩

end Yulang.GeneralDeclarativeRecordConsumption330
