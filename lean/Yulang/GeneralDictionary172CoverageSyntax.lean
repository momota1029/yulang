import Yulang.GeneralDictionary172CoverageInputExample

/-! Executable recognition is exact for the explicitly limited unary-spine
syntax. It is not a language acceptance/rejection test. -/
namespace Yulang.GeneralDictionary172CoverageSyntax
open GeneralNominalInspection (Query)
open GeneralDictionary172CoverageInput

def leafArguments : List Query → List Nat → Bool
  | [], [] => true
  | .variables actual :: queries, name :: names =>
      (actual == [name]) && leafArguments queries names
  | _, _ => false

theorem leafArguments_exact (queries : List Query) (names : List Nat) :
    leafArguments queries names = true ↔ queries = names.map (fun name => .variables [name]) := by
  induction names generalizing queries with
  | nil => cases queries <;> simp [leafArguments]
  | cons name names ih =>
    cases queries with
    | nil => simp [leafArguments]
    | cons query queries =>
      cases query <;> simp [leafArguments,ih]

def recognize (names : Fin n → Nat) (query : Query) : Bool :=
  match query with
  | .nominal _ children =>
      if leafArguments children (List.ofFn names) then true
      else match children with
        | [child] => recognize names child
        | _ => false
  | _ => false
termination_by sizeOf query

theorem recognize_nominal (names : Fin n → Nat) (tag : Nat) (children : List Query) :
    recognize names (.nominal tag children) =
      (if leafArguments children (List.ofFn names) then true
       else match children with | [child] => recognize names child | _ => false) := by
  cases children with
  | nil => rw [recognize]; simp
  | cons child rest => cases rest <;> rw [recognize] <;> simp

theorem recognize_sound (names : Fin n → Nat) (query : Query)
    (accepted : recognize names query = true) : Syntax names query := by
  cases query with
  | variables => simp [recognize] at accepted
  | scalar => simp [recognize] at accepted
  | node => simp [recognize] at accepted
  | deferred => simp [recognize] at accepted
  | nominal name children =>
    by_cases leaf : leafArguments children (List.ofFn names) = true
    ·
      have equal := (leafArguments_exact children (List.ofFn names)).mp leaf
      rw [List.map_ofFn] at equal
      subst children
      exact .leaf name
    · cases children with
      | nil => simp [recognize,leaf] at accepted
      | cons child rest =>
        cases rest with
        | nil =>
          have sub : recognize names child = true := by simpa [recognize,leaf] using accepted
          exact .wrap name (recognize_sound names child sub)
        | cons => simp [recognize,leaf] at accepted
termination_by sizeOf query

theorem recognize_complete (names : Fin n → Nat) (form : Syntax names query) :
    recognize names query = true := by
  induction form with
  | leaf name =>
    have equal : leafArguments (List.ofFn fun i => Query.variables [names i]) (List.ofFn names) = true :=
      (leafArguments_exact _ _).mpr (by simp only [List.map_ofFn]; rfl)
    rw [recognize_nominal]
    simp [equal]
  | wrap name inner ih => simp [recognize,ih]

theorem recognize_exact (names : Fin n → Nat) (query : Query) :
    recognize names query = true ↔ Syntax names query :=
  ⟨recognize_sound names query,recognize_complete names⟩

/-- Failed syntax recognition excludes only this certificate grammar. -/
theorem recognize_false (names : Fin n → Nat) (query : Query) :
    recognize names query = false ↔ ¬ Syntax names query := by
  rw [← recognize_exact]
  cases recognize names query <;> simp
/-- Actual successful inspection plus an executable syntax check recovers the
finite source certificate; callers supply neither Syntax nor a stored Spine. -/
theorem recognized_spine (state : GeneralNominalState.State) (names : Fin n → Nat)
    (accepted : recognize names query = true) (slot : Fin state.base.slots)
    (origin : Option GeneralNominalRecursiveInspection.Origin)
    (finished : GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveInspection.inspect state query (slot,slot) origin))
    (points : GeneralDictionary171LocalInspectionObservation.PointInspection state
      (GeneralNominalRecursiveInspection.inspect state query (slot,slot) origin)) :
    ∃ bounds : Fin n → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state names bounds slot, spine.query = query :=
  inspected_spine state names (recognize_sound names query accepted) slot origin finished points

theorem nested_recognized : recognize (fun _ : Fin 1 => 7)
    GeneralDictionaryNestedRefinementExamples.query = true := by decide +kernel

/-- The prior inhabited depth-two source exercises executable recognition and
actual inspection together, with no manually supplied syntactic derivation. -/
theorem computed_nested :
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds GeneralNominalProvenanceSource.state,
      ∃ spine : GeneralNominalSpineFacts.Spine GeneralNominalProvenanceSource.state (fun _ => 7) bounds 0,
        spine.query = GeneralDictionaryNestedRefinementExamples.query :=
  recognized_spine GeneralNominalProvenanceSource.state (fun _ => 7) nested_recognized 0 none
    GeneralDictionary172CoverageInputExample.actual_finished GeneralDictionary172CoverageInputExample.actual_points
end Yulang.GeneralDictionary172CoverageSyntax
