import Yulang.GeneralDictionaryFinishedInspection

/-! Finished nominal-only inspection survives fixed-carrier refinement even
when the normalized view changes. This is a strict query fragment, not general
refresh/reobserve invariance. Only existing recorded nominal descriptors are
used; variable leaves do not inspect their bounds. -/
namespace Yulang.GeneralDictionaryNominalOnlyRefresh175
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality
open GeneralDictionaryRefreshDescriptors
open GeneralDictionaryRefinementInspectionFacts
open GeneralDictionaryFinishedRefresh

inductive NominalOnly : Query → Prop where
  | variables (names : List Nat) : NominalOnly (.variables names)
  | nominal (name : Nat) (patterns : List Query) :
      (∀ query ∈ patterns, NominalOnly query) → NominalOnly (.nominal name patterns)

mutual
 theorem inspect_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
    (allowed : NominalOnly query)
    (finished : Finished (inspect context.state query bounds origin)) :
    inspect (reobserve context next).state query bounds origin =
      transferReport context next (inspect context.state query bounds origin) := by
  cases query with
  | variables names => simp only [inspect,transferReport,capture,List.map_map,Function.comp_def]
  | deferred => cases allowed
  | scalar => cases allowed
  | node => cases allowed
  | nominal expected patterns =>
    have childAllowed : ∀ q ∈ patterns, NominalOnly q := by cases allowed; assumption
    obtain ⟨lower,recorded⟩ := finished_nominal_lower context.state expected patterns bounds origin finished
    obtain ⟨upper,upperRecorded⟩ := finished_nominal_upper context.state expected patterns bounds origin finished
    have low := descriptor_preserved context next refinement bounds.1 lower recorded
    have high := descriptor_preserved context next refinement bounds.2 upper upperRecorded
    simp only [inspect,recorded,upperRecorded] at finished
    simp only [inspect,reobserve,recorded,upperRecorded,low,high]
    split
    · rename_i lowName
      split
      · rfl
      · rename_i arguments arguments_eq
        split
        · rename_i point
          rw [inspectMany_finished context next refinement patterns arguments _ _ childAllowed (by simpa only [lowName,arguments_eq,point,ite_true,finished_visit] using finished)]
          rfl
        · rename_i nonpoint
          split
          · rename_i highName
            split
            · rfl
            · rename_i targets targets_eq
              simp only [lowName,highName,arguments_eq,nonpoint,ite_false,targets_eq,ite_true,finished_visit] at finished
              have both := (finished_append _ _).mp finished
              rw [inspectMany_finished context next refinement patterns arguments _ _ childAllowed both.1,
                inspectMany_finished context next refinement patterns targets _ _ childAllowed both.2]
              simp only [transfer_visit,transfer_append]
          · rfl
    · rfl
 termination_by sizeOf query
 theorem inspectMany_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
    (allowed : ∀ query ∈ queries, NominalOnly query)
    (finished : Finished (inspectMany context.state queries bounds origins index)) :
    inspectMany (reobserve context next).state queries bounds origins index =
      transferReport context next (inspectMany context.state queries bounds origins index) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany,transferReport] <;> rfl
  | cons query queries =>
    cases bounds with
    | nil => simp only [inspectMany,transferReport]; rfl
    | cons bound bounds =>
      simp only [inspectMany] at finished
      have both := (finished_append _ _).mp finished
      rw [inspectMany,inspectMany,
        inspect_finished context next refinement query bound (origins index)
          (allowed query (by simp)) both.1,
        inspectMany_finished context next refinement queries bounds origins (index+1)
          (fun q h => allowed q (by simp [h])) both.2,transfer_append]
 termination_by sizeOf queries
end

/-- The declaration's translated query forest uses no structural/scalar test.
This is a syntactic sufficient fragment, not a language restriction. -/
def DeclarationFragment (context : Context) (declaration : GeneralDeclarations.Declaration) : Prop :=
  ∀ query ∈ GeneralNominalInspection.queries context.state context.interpretation declaration,
    NominalOnly query

theorem report_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds context.state))
    (allowed : DeclarationFragment context declaration)
    (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds)) :
    GeneralNominalRecursiveCandidates.report (reobserve context next) declaration bounds =
      transferReport context next (GeneralNominalRecursiveCandidates.report context declaration bounds) := by
  unfold GeneralNominalRecursiveCandidates.report at finished ⊢
  have queries : GeneralNominalInspection.queries (reobserve context next).state
      (reobserve context next).interpretation declaration =
      GeneralNominalInspection.queries context.state context.interpretation declaration := rfl
  rw [queries]
  rw [inspectMany_finished context next refinement _ bounds (fun _ => none) 0 allowed finished]
  rfl

/-- Exact current Instance transport: same model/key/ordered children. No view
identity or equality of computed inspection reports is assumed. -/
theorem instance_refinement (registry : GeneralDeclarations.Registry)
    (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (allowed : ∀ declaration ∈ registry.declarations, DeclarationFragment context declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := report_finished context next refinement declaration bounds (allowed declaration visible) finished
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]
    exact finished
  · unfold GeneralNominalRecursiveCandidates.RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]
    exact ready
  · rw [reports,transferred_bindings]
    exact emitted

/-- Whole source witness, under the explicit nominal-only registry fragment.
This transports a given completed dictionary, not existence of one. -/
theorem evidence_refinement (registry : GeneralDeclarations.Registry)
    (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (allowed : ∀ declaration ∈ registry.declarations, DeclarationFragment context declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload := by
  obtain ⟨tree,readback,given⟩ := old
  refine ⟨tree,readback,?_⟩
  exact GeneralSourceDictionaries.evidence_mono _ _
    (fun occurrence key children rule => instance_refinement registry context next refinement allowed model valid
      occurrence key children rule) given

end Yulang.GeneralDictionaryNominalOnlyRefresh175
