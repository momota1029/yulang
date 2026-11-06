import Yulang.Common
import Yulang.SourceDataRuntime

/-!
# Strict runtime readout on the same common syntax

This interpretation reads the finite data values of `SourceDataRuntime`. It
does not define producer subtyping and is not quotiented by producer demand
equivalence. Its constructor rules give the images of evaluated operands.
In particular a default requires a fallback value even if the source already
contains its field. Functions remain observable by `Common.AcceptAt`; the
first-order data runtime has no function value constructor.

Masks erase outer field constraints. They keep the same mask on record tails
and reset it on payload references. This operation is structural, not a
function on the unmasked set of runtime values.
-/

namespace Yulang.Common

open SourceDataRuntime

mutual
  inductive MaskedDataReadout : List Nat → Ty → Value → Prop where
    | base (hidden : List Nat) (scalar : Inference.Base) :
        MaskedDataReadout hidden (.base scalar) (.base scalar)
    | top (hidden : List Nat) (value : Value) : MaskedDataReadout hidden .top value
    | unionLeft : MaskedDataReadout hidden first value →
        MaskedDataReadout hidden (.union first last) value
    | unionRight : MaskedDataReadout hidden last value →
        MaskedDataReadout hidden (.union first last) value
    | inter : MaskedDataReadout hidden first value → MaskedDataReadout hidden last value →
        MaskedDataReadout hidden (.inter first last) value
    | pair : StateDataReadout first left → StateDataReadout last right →
        MaskedDataReadout hidden (.pair first last) (.pair left right)
    | width (hidden : List Nat) (fields : List (Nat × Value)) :
        MaskedDataReadout hidden .emptyRecord (.record fields)
    | exact (hidden : List Nat) (fields : List (Nat × Value))
        (onlyHidden : ∀ field ∈ fields, field.1 ∈ hidden) :
        MaskedDataReadout hidden .exactEmpty (.record fields)
    | recordVisible (visible : label ∉ hidden) :
        StateDataReadout payload value → MaskedDataReadout hidden rest (.record fields) →
        MaskedDataReadout hidden (.record label payload rest)
          (.record (Fields.insert label value fields))
    | recordHidden (invisible : label ∈ hidden) :
        MaskedDataReadout hidden rest (.record fields) →
        MaskedDataReadout hidden (.record label payload rest) (.record fields)
    | defaultVisible (visible : label ∉ hidden) :
        MaskedDataReadout hidden source (.record fields) → StateDataReadout fallback value →
        MaskedDataReadout hidden (.recordDefault label source fallback)
          (.record (Fields.insertDefault label value fields))
    | defaultHidden (invisible : label ∈ hidden) :
        MaskedDataReadout hidden source (.record fields) →
        MaskedDataReadout hidden (.recordDefault label source fallback) (.record fields)
    | variant : StateDataReadout payload value →
        MaskedDataReadout hidden (.variant label payload) (.variant label value)
    | mask : MaskedDataReadout (hidden ++ more) source value →
        MaskedDataReadout hidden (.mask more source) value

  inductive StateDataReadout : CommonSyntax.State Row → Value → Prop where
    | unfold : MaskedDataReadout [] (CommonSyntax.graph Row state) value →
        StateDataReadout state value
end

def DataReadout (type : Ty) (value : Value) : Prop := MaskedDataReadout [] type value

theorem quote_data_exact (type : Ty) (value : Value) :
    StateDataReadout (.node type) value ↔ DataReadout type value := by
  constructor
  · intro read
    cases read with
    | unfold read => exact read
  · intro read
    exact .unfold read

theorem exactEmpty_data_exact (value : Value) :
    DataReadout exactEmpty value ↔ value = .record [] := by
  constructor
  · intro read
    cases read with
    | exact _ fields onlyHidden =>
        have empty : fields = [] := by
          cases fields with
          | nil => rfl
          | cons first rest =>
              have impossible := onlyHidden first (by simp)
              simp at impossible
        rw [empty]
  · intro same
    subst value
    exact .exact [] [] (by simp)

theorem width_data_exact (value : Value) :
    DataReadout emptyRecord value ↔ ∃ fields, value = .record fields := by
  constructor
  · intro read
    cases read with
    | width _ fields => exact ⟨fields, rfl⟩
  · rintro ⟨fields, rfl⟩
    exact .width [] fields

theorem record_data_image (label : Nat) (payload rest : Ty) (result : Value) :
    DataReadout (record label payload rest) result ↔
      ∃ value fields, DataReadout payload value ∧ DataReadout rest (.record fields) ∧
        result = .record (Fields.insert label value fields) := by
  constructor
  · intro read
    cases read with
    | recordVisible _ first last =>
        exact ⟨_, _, (quote_data_exact _ _).mp first, last, rfl⟩
    | recordHidden impossible _ => simp at impossible
  · rintro ⟨value, fields, first, last, rfl⟩
    exact .recordVisible (by simp) ((quote_data_exact _ _).mpr first) last

theorem default_data_image (label : Nat) (source fallback : Ty) (result : Value) :
    DataReadout (recordDefault label source fallback) result ↔
      ∃ fields value, DataReadout source (.record fields) ∧ DataReadout fallback value ∧
        result = .record (Fields.insertDefault label value fields) := by
  constructor
  · intro read
    cases read with
    | defaultVisible _ first last =>
        exact ⟨_, _, first, (quote_data_exact _ _).mp last, rfl⟩
    | defaultHidden impossible _ => simp at impossible
  · rintro ⟨fields, value, first, last, rfl⟩
    exact .defaultVisible (by simp) first ((quote_data_exact _ _).mpr last)

theorem exactEmpty_data_ne_width :
    ¬ (∀ value, DataReadout exactEmpty value ↔ DataReadout emptyRecord value) := by
  intro same
  have nonempty : DataReadout emptyRecord (.record [(0, .base .int)]) := .width [] _
  have empty := (exactEmpty_data_exact _).mp ((same _).mpr nonempty)
  cases empty

theorem default_bottom_fallback (label : Nat) (source : Ty) (result : Value) :
    ¬ DataReadout (recordDefault label source .bottom) result := by
  rw [default_data_image]
  rintro ⟨_, _, _, impossible, _⟩
  cases impossible

theorem default_bottom_source (label : Nat) (fallback : Ty) (result : Value) :
    ¬ DataReadout (recordDefault label .bottom fallback) result := by
  rw [default_data_image]
  rintro ⟨_, _, impossible, _, _⟩
  cases impossible

theorem default_inhabited_iff (label : Nat) (source fallback : Ty) :
    (∃ result, DataReadout (recordDefault label source fallback) result) ↔
      (∃ fields, DataReadout source (.record fields)) ∧
      (∃ value, DataReadout fallback value) := by
  constructor
  · rintro ⟨result, read⟩
    obtain ⟨fields, value, first, last, _⟩ := (default_data_image label source fallback result).mp read
    exact ⟨⟨fields, first⟩, ⟨value, last⟩⟩
  · rintro ⟨⟨fields, first⟩, ⟨value, last⟩⟩
    exact ⟨_, (default_data_image _ _ _ _).mpr ⟨fields, value, first, last, rfl⟩⟩

theorem default_present_data (label : Nat) (source fallback : Ty)
    (fields : List (Nat × Value)) (existing value : Value)
    (first : DataReadout source (.record fields)) (last : DataReadout fallback value)
    (present : Fields.lookup label fields = some existing) :
    DataReadout (recordDefault label source fallback) (.record fields) := by
  apply (default_data_image _ _ _ _).mpr
  exact ⟨fields, value, first, last, congrArg Value.record
    (Fields.insertDefault_present label value existing fields present).symm⟩

theorem mask_data_exact (hidden : List Nat) (type : Ty) (value : Value) :
    DataReadout (mask hidden type) value ↔ MaskedDataReadout hidden type value := by
  constructor
  · intro read
    cases read with
    | mask read => exact read
  · intro read
    exact .mask read

end Yulang.Common
