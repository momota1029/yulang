import Yulang.CommonCanonicalTemplatePrograms

namespace Yulang.CommonCanonicalGridPrograms

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalWordPrograms
open CommonCanonicalRangeEmitters
open CommonCanonicalTemplatePrograms

structure GridContext (registers parameters : Nat) where
  base : Context registers parameters
  coordinate : Fin (registers + 1)
  fuel : Fin (registers + 1)
  coordinateFuel : coordinate ≠ fuel
  coordinateOutput : coordinate ≠ base.output
  fuelOutput : fuel ≠ base.output
  coordinateWork : ∀ index, coordinate ≠ base.work index
  fuelWork : ∀ index, fuel ≠ base.work index
  inputsCoordinate : ∀ index, base.inputs index ≠ coordinate
  inputsFuel : ∀ index, base.inputs index ≠ fuel

def GridContext.extended {registers parameters : Nat} (context : GridContext registers parameters) :
    Context registers (parameters + 2) where
  inputs := rangeInputs context.base.inputs context.coordinate context.fuel
  output := context.base.output
  work := context.base.work
  distinct := context.base.distinct
  outputOutside := context.base.outputOutside
  inputsOutside := by
    intro parameter index
    refine Fin.addCases (fun old => ?_) (fun extra => ?_) parameter
    · simpa only [rangeInputs, Fin.addCases_left] using context.base.inputsOutside old index
    · refine Fin.cases ?_ (fun _ => ?_) extra
      · simpa only [rangeInputs, Fin.addCases_right, Fin.cases_zero] using context.coordinateWork index
      · simpa only [rangeInputs, Fin.addCases_right, Fin.cases_succ] using context.fuelWork index
  inputsOutput := by
    intro parameter
    refine Fin.addCases (fun old => ?_) (fun extra => ?_) parameter
    · simpa only [rangeInputs, Fin.addCases_left] using context.base.inputsOutput old
    · refine Fin.cases ?_ (fun _ => ?_) extra
      · simpa only [rangeInputs, Fin.addCases_right, Fin.cases_zero] using context.coordinateOutput
      · simpa only [rangeInputs, Fin.addCases_right, Fin.cases_succ] using context.fuelOutput

def gridBody (parameters : Nat) (excluded : Option (Fin parameters)) : Template (parameters + 2) :=
  let entry := Template.append (.literal [.cons]) (.number (Fin.natAdd parameters 0))
  match excluded with
  | none => entry
  | some omitted => .choose (Fin.natAdd parameters 0) (omitted.castAdd 2) (.literal []) entry

def gridEntry {parameters : Nat} (excluded : Option (Fin parameters))
    (environment : Environment parameters) (coordinate : Nat) : Word :=
  match excluded with
  | none => .cons :: natural coordinate
  | some omitted => if coordinate = environment omitted then [] else .cons :: natural coordinate

def gridList {registers parameters : Nat} (context : GridContext registers parameters)
    (bound : Fin parameters) (excluded : Option (Fin parameters)) : Routine registers :=
  append (rangeEmit (context.base.inputs bound) context.coordinate context.fuel (context.base.work 1)
    ((gridBody parameters excluded).compile context.extended))
    (emit context.base.output (context.base.work 1) [.nil])

/-- Full and omitted-coordinate lists are produced by an actual bounded
counter loop, including their list delimiters. -/
theorem gridList_emits {registers parameters : Nat} (context : GridContext registers parameters)
    (bound : Fin parameters) (excluded : Option (Fin parameters)) :
    Emits (gridList context bound excluded) context.base.inputs context.base.output
      (fun environment => rangeTokens (gridEntry excluded environment) 0 (environment bound + 1) ++ [.nil]) := by
  have bodyCorrect : Emits ((gridBody parameters excluded).compile context.extended)
      (rangeInputs context.base.inputs context.coordinate context.fuel) context.base.output
      (fun environment => gridEntry excluded (fun index => environment (index.castAdd 2))
        (environment (Fin.natAdd parameters 0))) := by
    have correct := template_emits context.extended (gridBody parameters excluded)
    cases excluded <;> simpa only [GridContext.extended, gridBody, Template.tokens, gridEntry, List.singleton_append,
      List.nil_append] using correct
  have rangeCorrect := emits_range context.base.inputs context.base.output context.coordinate context.fuel
    (context.base.work 1) context.coordinateFuel (context.fuelWork 1)
    (Ne.symm context.coordinateOutput) (Ne.symm context.fuelOutput) (context.base.outputOutside 1)
    (fun index => ⟨context.inputsCoordinate index, context.inputsFuel index, context.base.inputsOutside index 1⟩)
    bound ((gridBody parameters excluded).compile context.extended) (gridEntry excluded) bodyCorrect
  exact emits_append rangeCorrect (emits_literal context.base.inputs context.base.output (context.base.work 1)
    (context.base.outputOutside 1) (fun index => ⟨context.base.inputsOutput index, context.base.inputsOutside index 1⟩)
    [.nil])

/-- The emitted coordinate-list words are precisely the existing finite
closed-row syntax, both for the whole natural grid and each zero plane. -/
theorem grid_serialization_exact (scopes parameters : Nat) :
    row (CommonCanonicalCounterConstraints.gridRow : CommonCanonicalRowSyntax.Row scopes parameters) =
      .rowClosed :: (rangeTokens (fun coordinate => .cons :: natural coordinate) 0 scopes ++ [.nil]) ∧
    ∀ excluded : Fin scopes,
      row (CommonCanonicalCounterConstraints.zeroRow excluded : CommonCanonicalRowSyntax.Row scopes parameters) =
        .rowClosed :: (rangeTokens (fun coordinate =>
          if coordinate = excluded.val then [] else .cons :: natural coordinate) 0 scopes ++ [.nil]) := by
  have finRangeValues (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i left right
      simp
  have filteredValues (n : Nat) (excluded : Fin n) :
      ((List.finRange n).filter (fun coordinate => coordinate != excluded)).map Fin.val =
        (List.range n).filter (fun coordinate => coordinate != excluded.val) := by
    rw [← finRangeValues, List.filter_map]
    rfl
  have listMap {α β : Type} (encode : β → Word) (mapping : α → β) (values : List α) :
      list encode (values.map mapping) = list (fun value => encode (mapping value)) values := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp only [List.map_cons, list, ih]
  have rangeList (start count : Nat) :
      list natural (List.range' start count) =
        rangeTokens (fun coordinate => .cons :: natural coordinate) start count ++ [.nil] := by
    induction count generalizing start with
    | zero => simp [list, rangeTokens]
    | succ count ih => simp [List.range'_succ, list, rangeTokens, ih, List.append_assoc]
  have rangeFilter (start count excluded : Nat) :
      list natural ((List.range' start count).filter (fun coordinate => coordinate != excluded)) =
        rangeTokens (fun coordinate => if coordinate = excluded then [] else .cons :: natural coordinate)
          start count ++ [.nil] := by
    induction count generalizing start with
    | zero => simp [list, rangeTokens]
    | succ count ih =>
      by_cases same : start = excluded
      · simp [List.range'_succ, same, rangeTokens, ih]
      · simp [List.range'_succ, same, rangeTokens, list, ih, List.append_assoc]
  constructor
  · change .rowClosed :: list (fun coordinate : Fin scopes => natural coordinate.val) (List.finRange scopes) = _
    rw [← listMap natural Fin.val, finRangeValues, List.range_eq_range', rangeList]
  · intro excluded
    change .rowClosed :: list (fun coordinate : Fin scopes => natural coordinate.val)
      ((List.finRange scopes).filter (fun coordinate => coordinate != excluded)) = _
    rw [← listMap natural Fin.val, filteredValues, List.range_eq_range', rangeFilter]

inductive Script (parameters : Nat) where
  | atom (template : Template parameters)
  | grid (bound : Fin parameters) (excluded : Option (Fin parameters))
  | append (first last : Script parameters)

def Script.tokens {parameters : Nat} : Script parameters → Environment parameters → Word
  | .atom template, environment => template.tokens environment
  | .grid bound excluded, environment =>
      rangeTokens (gridEntry excluded environment) 0 (environment bound + 1) ++ [.nil]
  | .append first last, environment => first.tokens environment ++ last.tokens environment

def Script.compile {registers parameters : Nat} (context : GridContext registers parameters) :
    Script parameters → Routine registers
  | .atom template => template.compile context.base
  | .grid bound excluded => gridList context bound excluded
  | .append first last => Routine.append (first.compile context) (last.compile context)

theorem script_emits {registers parameters : Nat} (context : GridContext registers parameters)
    (script : Script parameters) :
    Emits (script.compile context) context.base.inputs context.base.output script.tokens := by
  induction script with
  | atom template => exact template_emits context.base template
  | grid bound excluded => exact gridList_emits context bound excluded
  | append first last firstCorrect lastCorrect => exact emits_append firstCorrect lastCorrect

end Yulang.CommonCanonicalGridPrograms
