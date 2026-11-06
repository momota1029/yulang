import Yulang.NominalListSpread

/-!
# Concrete finite-list spread witnesses

The middle list and its elements are universally quantified. The complete
observation includes the spread expression even when it contributes no
elements. These examples select identity conversion explicitly; no source
cast policy or default nominal identity is inferred.
-/

namespace Yulang.NominalListSpreadExamples

open CaseValues EvaluationTrace NominalListSpread

def keep : Unit → Value F → Value F := fun _ value => value
def KeepTyped (_ : Unit) (input target : Ty F) : Prop := input = target

theorem keep_sound : ConversionSound (F := F) KeepTyped keep := by
  intro code input target same value valid
  subst target
  exact valid

def parts (first last : Value F) (middle : List (Value F)) : List (DataPart F Unit) :=
  [.element (.value first) (), .spread (.value (.list middle)), .element (.value last) ()]

theorem parts_typed (types : List (Nat × Ty F)) (target : Ty F)
    (first last : Value F) (middle : List (Value F))
    (firstValid : target first) (lastValid : target last)
    (middleValid : ∀ value ∈ middle, target value) :
    Typing (CaseDataTerms.Typing types) KeepTyped (parts first last middle) target := by
  refine .cons (.element (.widen .value ?_) rfl) (.cons (.spread (.widen .value ?_))
    (.cons (.element (.widen .value ?_) rfl) .nil))
  · intro value same; cases same; exact firstValid
  · intro value same; cases same; exact middleValid
  · intro value same; cases same; exact lastValid

/-- The spread source appears once between the two ordinary sources, even
when `middle = []`. No value is removed or reordered by flattening. -/
theorem middle_spread_trace (environment : Bindings F) (first last : Value F) (middle : List (Value F)) :
    eval keep environment (parts first last middle) =
      ⟨[.source (.value first), .source (.value (.list middle)), .source (.value last)],
        .ok (.list (first :: (middle ++ [last])))⟩ := rfl

theorem typed_middle_progress (types : List (Nat × Ty F)) (target : Ty F)
    (first last : Value F) (middle : List (Value F))
    (firstValid : target first) (lastValid : target last)
    (middleValid : ∀ value ∈ middle, target value)
    (environment : Bindings F) (valid : BindingsHold types environment) :
    ∃ values, eval keep environment (parts first last middle) =
      ⟨sourceTrace (CaseDataTerms.eval environment) (parts first last middle), .ok (.list values)⟩ ∧
      Ty.list target (.list values) :=
  data_typing_evaluates keep keep_sound (parts_typed types target first last middle firstValid lastValid middleValid)
    environment valid

theorem consecutive_spreads (environment : Bindings F) (left right : List (Value F)) :
    eval (keep : Unit → Value F → Value F) environment
      [.spread (.value (.list left)), .spread (.value (.list right))] =
      ⟨[.source (.value (.list left)), .source (.value (.list right))], .ok (.list (left ++ right))⟩ := by
  simp [eval, run, runPart, Part.source, CaseDataTerms.eval, Logged.bind, Logged.prepend,
    CaseDataTerms.pure, Logged.ofResult, expand]

theorem middle_spread_index (first last : Value F) (middle : List (Value F))
    (position : Nat) (value : Value F) (found : NominalListViews.At middle position value) :
    NominalListViews.index (first :: (middle ++ [last])) (position + 1) = some value := by
  have present := (NominalListViews.index_exact middle position value).mpr found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp
    (show middle[position]? = some value from present)
  simpa [NominalListViews.index, List.getElem?_append, bound] using present

end Yulang.NominalListSpreadExamples
