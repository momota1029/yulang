import Yulang.GeneralDictionaryActualSchemaScope
import Yulang.GeneralNominalCaptureCoverage183
import Yulang.GeneralNominalHeadMatchMass
import Yulang.GeneralNominalTemplateSubstitution

/-! Finished inspection excludes deferred queries at every nested position.
This syntactic completeness is stronger than the inspected/test-count equality
of centered inspection and does not require a model or covered-head premise. -/
namespace Yulang.GeneralNominalCompleteNames183
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalInspectionAlignment
open GeneralNominalHeadMatchMass (Complete)

mutual
  theorem inspect_complete (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin)
      (finished : Finished (inspect state query bounds origin)) : Complete query := by
    cases query with
    | variables | scalar => simp only [Complete]
    | deferred =>
      simp only [inspect,Finished,block] at finished
      cases finished.1
    | node shape children =>
      simp only [Complete]
      simp only [inspect,finished_visit] at finished
      split at finished
      · split at finished
        · exact many_complete state children _ _ 0 finished
        · simp only [Finished,block] at finished
          cases finished.1
      · simp only [Finished] at finished
        cases finished.2.1
      · simp only [Finished,block] at finished
        cases finished.1
    | nominal key children =>
      simp only [Complete]
      obtain ⟨descriptor,intervals,recorded,same,found,complete,included⟩ :=
        nominal_left state children bounds origin finished
      exact many_complete state children intervals _ 0 complete
  termination_by sizeOf query

  theorem many_complete (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (finished : Finished (inspectMany state queries bounds origins offset)) :
      ∀ query ∈ queries, Complete query := by
    cases queries with
    | nil => intro query member; cases member
    | cons query rest =>
      cases bounds with
      | nil =>
        simp only [inspectMany,Finished] at finished
        cases finished.2.2
      | cons head tail =>
        simp only [inspectMany] at finished
        have parts := (finished_append ..).mp finished
        intro other member
        rcases List.mem_cons.mp member with same | later
        · exact same.symm ▸ inspect_complete state query head (origins offset) parts.1
        · exact many_complete state rest tail origins (offset+1) parts.2 other later
  termination_by sizeOf queries
end

open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalCaptureNames (names manyNames)

private theorem many_names_flat (queries : List Query) :
    manyNames queries = queries.flatMap names := by
  induction queries with
  | nil => rfl
  | cons q qs ih => simp only [manyNames,List.flatMap_cons,ih]

private theorem argument_names_flat (patterns : List Pattern) :
    variablesArgs patterns = patterns.flatMap Pattern.variables := by
  induction patterns with
  | nil => rfl
  | cons p ps ih => simp only [variablesArgs,List.flatMap_cons,ih]

private theorem plain_names (pattern : Pattern) (binders : List Nat)
    (found : GeneralCandidateInspection.plainNames pattern = some binders) : binders = pattern.variables := by
  cases pattern with
  | var n => simpa [GeneralCandidateInspection.plainNames,Pattern.variables] using found.symm
  | app | record | variant => simp [GeneralCandidateInspection.plainNames] at found
  | join first last =>
    simp only [GeneralCandidateInspection.plainNames] at found
    cases one : GeneralCandidateInspection.plainNames first with
    | none => simp [one] at found
    | some xs =>
      cases two : GeneralCandidateInspection.plainNames last with
      | none => simp [one,two] at found
      | some ys =>
        simp [one,two] at found
        subst binders
        rw [Pattern.variables,plain_names first xs one,plain_names last ys two]
termination_by sizeOf pattern

/-- Every pattern variable survives a complete translation, even for terminal
heads for which declaration checking supplies no child-count restriction. -/
theorem translated_names (constructors : Constructors) (interpretation : Interpretation)
    (pattern : Pattern) (complete : Complete (translate constructors interpretation pattern))
    (name : Nat) (member : name ∈ pattern.variables) :
    name ∈ names (translate constructors interpretation pattern) := by
  fun_induction translate constructors interpretation pattern with
  | case1 n => exact member
  | case2 tag payload ih =>
    cases found : GeneralCandidateInspection.plainNames payload with
    | none =>
      simp only [found,Complete] at complete
      simp only [names,manyNames,List.append_nil]
      exact ih (complete _ (List.mem_singleton_self _)) member
    | some binders =>
      simp only [names,manyNames,List.append_nil]
      rwa [plain_names payload binders found]
  | case3 key base h => cases member
  | case4 key h => cases member
  | case5 key h => cases member
  | case6 key first last h ih1 ih2 =>
    simp only [Complete] at complete
    simp only [names,manyNames,List.append_nil]
    have members : name ∈ first.variables ∨ name ∈ last.variables := by
      simpa only [Pattern.variables,variablesArgs,List.append_nil,List.mem_append] using member
    rcases members with one | two
    · exact List.mem_append_left _ (ih1 (complete _ (List.mem_cons_self ..)) one)
    · exact List.mem_append_right _ (ih2 (complete _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) two)
  | case7 key actuals declaration hc good h1 h2 h3 h4 ih =>
    simp only [Complete] at complete
    simp only [names,many_names_flat]
    rw [Pattern.variables,argument_names_flat] at member
    obtain ⟨arg,present,used⟩ := List.mem_flatMap.mp member
    have translated := ih ⟨arg,present⟩ (complete _ (List.mem_map.mpr ⟨⟨arg,present⟩,List.mem_attach ..,rfl⟩)) used
    exact List.mem_flatMap.mpr ⟨_,List.mem_map.mpr ⟨⟨arg,present⟩,List.mem_attach ..,rfl⟩,translated⟩
  | case8 | case9 | case11 | case12 => simp only [Complete] at complete
  | case10 label payload tail labels children ht fields iht ihp =>
    have length := GeneralNominalClosedPatternNormal.record_length tail ht
    have parts := GeneralNominalTemplateSubstitution.record_complete label _ labels children length complete
    simp only [names,many_names_flat]
    rcases List.mem_append.mp member with one | two
    · exact List.mem_flatMap.mpr ⟨_,List.mem_map.mpr ⟨_,List.mem_mergeSort.mpr (List.mem_cons_self ..),rfl⟩,ihp parts.1 one⟩
    · have rest := iht (by rw [ht]; exact parts.2) two
      rw [ht,names,many_names_flat] at rest
      obtain ⟨child,present,used⟩ := List.mem_flatMap.mp rest
      have mapped : child ∈ (labels.zip children).map Prod.snd := by
        rw [List.map_snd_zip (Nat.le_of_eq length)]
        exact present
      obtain ⟨field,within,equal⟩ := List.mem_map.mp mapped
      exact List.mem_flatMap.mpr ⟨child,List.mem_map.mpr ⟨field,
        List.mem_mergeSort.mpr (List.mem_cons_of_mem _ within),equal⟩,used⟩

 theorem translated_many_names (constructors : Constructors) (interpretation : Interpretation)
    (patterns : List Pattern)
    (complete : ∀ pattern ∈ patterns, Complete (translate constructors interpretation pattern))
    (name : Nat) (member : name ∈ variablesArgs patterns) :
    name ∈ manyNames (patterns.map (translate constructors interpretation)) := by
  rw [argument_names_flat] at member
  obtain ⟨pattern,present,used⟩ := List.mem_flatMap.mp member
  rw [many_names_flat]
  exact List.mem_flatMap.mpr ⟨_,List.mem_map.mpr ⟨pattern,present,rfl⟩,
    translated_names constructors interpretation pattern (complete pattern present) name used⟩

/-- The completeness premise is supplied by the actual finished inspection,
not by a separate language-fragment restriction. -/
theorem finished_translated_names (state : GeneralNominalState.State)
    (interpretation : Interpretation) (patterns : List Pattern)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state (patterns.map (translate state.constructors interpretation)) bounds origins offset))
    (name : Nat) (member : name ∈ variablesArgs patterns) :
    name ∈ manyNames (patterns.map (translate state.constructors interpretation)) := by
  apply translated_many_names state.constructors interpretation patterns _ name member
  intro pattern present
  exact many_complete state _ bounds origins offset finished _ (List.mem_map.mpr ⟨pattern,present,rfl⟩)

/-- Every declared input name has a concrete capture when the whole head
inspection finishes. In particular this includes terminal declarations. -/
theorem declaration_input_capture (state : GeneralNominalState.State)
    (interpretation : Interpretation) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state (queries state interpretation declaration) bounds origins offset))
    (name : Nat) (member : name ∈ declaration.inputNames) :
    ∃ captured ∈ (inspectMany state (queries state interpretation declaration) bounds origins offset).captures,
      captured.name = name := by
  apply GeneralNominalCaptureCoverage183.many_covers state _ bounds origins offset finished name
  exact finished_translated_names state interpretation (normalizeArgs declaration.head) bounds origins offset finished name member

end Yulang.GeneralNominalCompleteNames183
