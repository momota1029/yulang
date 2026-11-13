import Yulang.GeneralNominalUniformChildProduction

/-! Exposed queries retain original declaration subpatterns and their keys.
Actual full-report tests provide heads at named origins. Scalar exposure is a
complete zero-child replacement case over the surviving original holes. -/
namespace Yulang.GeneralNominalExposureSources
open GeneralDeclarationPatterns GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds translate)
open GeneralNominalOriginTerms GeneralNominalSourcePatternParts GeneralNominalUniformReportDispatch
open GeneralNominalFiniteMeaning GeneralNominalHoleElimination GeneralNominalIndexedHoleReadback

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty}
variable {origins : Nat → Origin}
variable {state : GeneralNominalState.State} {report : Report state}
variable {origin : Option Origin} {remaining : List Nat} {inventory : Inventory}

def SourceQuery (context : GeneralNominalCandidates.Context) (sources : List Pattern) (query : Query) : Prop :=
  ∃ original ∈ sources, ∃ pattern, Part original pattern ∧ covered pattern = true ∧
    translate context.state.constructors context.interpretation pattern = query

theorem source_query_children (member : child ∈ queryChildren parent)
    (known : SourceQuery context sources parent) : SourceQuery context sources child := by
  obtain ⟨original,present,pattern,part,covered,translated⟩ := known
  rw [← translated] at member
  obtain ⟨source,subpart,equal⟩ := GeneralNominalOpenReification.child_source pattern covered member
  exact ⟨original,present,source,part_trans part subpart,GeneralNominalOpenReification.part_covered subpart covered,equal⟩

theorem source_query_roots (covered : coveredArgs sources = true) :
    ∀ query ∈ sources.map (translate context.state.constructors context.interpretation), SourceQuery context sources query := by
  intro query member
  obtain ⟨pattern,present,rfl⟩ := List.mem_map.mp member
  exact ⟨pattern,present,pattern,.refl,GeneralNominalChildAssembly.covered_member _ covered _ present,rfl⟩

theorem source_query_scoped (known : SourceQuery context sources query)
    (scope : ∀ pattern ∈ sources, GeneralNominalSourceLabelVocabulary.Scoped keys pattern) :
    ∃ pattern, GeneralNominalSourceLabelVocabulary.Scoped keys pattern ∧ covered pattern = true ∧
      translate context.state.constructors context.interpretation pattern = query := by
  obtain ⟨original,member,pattern,part,covered,translated⟩ := known
  exact ⟨pattern,GeneralNominalSourceLabelVocabulary.part_scoped part (scope original member),covered,translated⟩

/-- Exhaustive traversal of the actual translated declaration forest retains
its original source queries in the exposure branch, including both endpoint
reports. The represented input forest remains an explicit premise. -/
theorem source_report_dispatch
    (inhabited : ∃ model, models model)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (bounds : List (Bounds state)) (actuals : Nat → Option Origin) (offset : Nat)
    (terms : List (Expr Nat)) (covered : coveredArgs sources = true)
    (finished : Finished (inspectMany state
      (sources.map (translate context.state.constructors context.interpretation)) bounds actuals offset))
    (known : GeneralNominalUniformInspectionInputs.InputsAt models values state actuals offset bounds terms)
    (labels : ∀ term ∈ terms, ∃ pattern, Sourced context remaining
      (GeneralNominalSourceLabelVocabulary.Allowed keys remaining) pattern term) :
    Captures context remaining (GeneralNominalSourceLabelVocabulary.Allowed keys remaining) models values
      (inspectMany state (sources.map (translate context.state.constructors context.interpretation)) bounds actuals offset) ∨
    ∃ hole ∈ remaining, Exposed models values (SourceQuery context sources)
      (inspectMany state (sources.map (translate context.state.constructors context.interpretation)) bounds actuals offset) hole :=
  GeneralNominalSourceLabelVocabulary.scoped_report_dispatch state (fun _ _ => source_query_children)
    inhabited valid _ bounds actuals offset terms (source_query_roots covered) finished known labels

theorem scalar_source (translated : translate constructors interpretation pattern = .scalar base) :
    ∃ key, pattern = .app key [] := by
  cases pattern with
  | var | variant | join => simp only [translate] at translated; cases translated
  | record => simp only [translate] at translated; split at translated <;> cases translated
  | app key arguments =>
    rw [translate.eq_def] at translated
    dsimp only at translated
    split at translated
    · exact ⟨key,rfl⟩
    · cases translated
    · cases translated
    · cases translated
    · split at translated
      · split at translated <;> cases translated
      · cases translated

theorem scalar_allowed (scope : GeneralNominalSourceLabelVocabulary.Scoped keys pattern)
    (translated : translate constructors interpretation pattern = .scalar base) :
    GeneralNominalSourceLabelVocabulary.Allowed keys remaining pattern := by
  obtain ⟨key,rfl⟩ := scalar_source translated
  exact ⟨scope,by intro name member; cases member⟩

def queryTest : Query → Test
  | .scalar base => .scalar base
  | .node shape _ => .structural shape
  | .nominal name queries => .nominal name queries.length
  | _ => .scalar .int

theorem constructor_visit (constructor : GeneralNominalOpenInspectionMatching.Constructor query) :
    ∃ body : Report state, inspect state query bounds origin = body.visit bounds origin (queryTest query) := by
  cases query with
  | variables | deferred => cases constructor
  | scalar | node | nominal => simp only [inspect,queryTest]; exact ⟨_,rfl⟩

theorem fragment_position (constructor : GeneralNominalOpenInspectionMatching.Constructor query)
    (inside : Fragment (inspect state query bounds origin) report) : bounds ∈ report.inspected := by
  obtain ⟨body,equal⟩ := constructor_visit (state := state) (bounds := bounds) (origin := origin) constructor
  apply (fragment_fields inside).2.1
  rw [equal]
  exact List.mem_cons_self ..

theorem fragment_test (constructor : GeneralNominalOpenInspectionMatching.Constructor query)
    (inside : Fragment (inspect state query bounds (some root)) report) :
    (root,bounds) ∈ report.anchors ∧ (root,queryTest query) ∈ report.tests := by
  obtain ⟨body,equal⟩ := constructor_visit (state := state) (bounds := bounds) (origin := some root) constructor
  constructor
  · apply (fragment_fields inside).2.2.1
    rw [equal]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · apply (fragment_fields inside).2.2.2
    rw [equal]
    exact List.mem_append_left _ (List.mem_singleton_self _)

theorem fragment_head (constructor : GeneralNominalOpenInspectionMatching.Constructor query)
    (inside : Fragment (inspect state query bounds (some root)) report)
    (valid : ∀ model, models model → ProjectionModels state report model) :
    ∀ model, models model → Head model root (queryTest query) := by
  have present := fragment_test constructor inside
  intro model holds
  exact ⟨((valid model holds).1 _ present.1).1,(valid model holds).2.1 _ present.2⟩

/-- Reification uses an original source subpattern, even when the exposure
was reached through a nominal endpoint fallback. -/
theorem exposed_source (exposed : Exposed models values (SourceQuery context sources) report hole) :
    ∃ query bounds origin original, original ∈ sources ∧ ∃ pattern,
      Part original pattern ∧ covered pattern = true ∧
      translate context.state.constructors context.interpretation pattern = query ∧
      GeneralNominalOpenInspectionMatching.Constructor query ∧
      Finished (inspect state query bounds origin) ∧
      Fragment (inspect state query bounds origin) report ∧ bounds ∈ report.inspected ∧
      GeneralNominalUniformInspectionInputs.Input models values state bounds origin (.leaf hole) := by
  obtain ⟨query,bounds,origin,⟨original,present,pattern,part,covered,translated⟩,constructor,finished,inside,known⟩ := exposed
  exact ⟨query,bounds,origin,original,present,pattern,part,covered,translated,constructor,finished,inside,
    fragment_position constructor inside,known⟩

/-- No child-representation premise is needed for scalar exposure. The
replacement is justified by the actual report and shares the original hole
origin uniformly across all relevant models. -/
theorem scalar_replacement
    (inside : Fragment (inspect state (.scalar base) bounds (some root)) report)
    (valid : ∀ model, models model → ProjectionModels state report model)
    (known : GeneralNominalUniformInspectionInputs.Input models values state bounds (some root) (.leaf hole))
    (member : hole ∈ remaining)
    (leafValues : ∀ model, models model → ∀ name ∈ remaining, At model .actual (origins name) (values model name))
    (covered : GeneralDeclarationPatterns.covered pattern = true)
    (translated : translate context.state.constructors context.interpretation pattern = .scalar base) :
    GeneralNominalUniformHoleLabels.Labelled models context origins (remaining.erase hole) (origins hole) pattern
      (.node (.scalar base) Fin.elim0) := by
  have previous := GeneralNominalUniformCaptureProduction.input_readback leafValues known
    (show Closed remaining (.leaf hole) from by intro name present; cases List.mem_singleton.mp present; exact member)
  have head := fragment_head (query := .scalar base) trivial inside valid
  refine ⟨⟨covered,translated,True.intro,fun position => Fin.elim0 position⟩,?_,?_⟩
  · intro model holds
    apply holds_transport (previous.1 model holds)
    exact ⟨head model holds,fun position => Fin.elim0 position⟩
  · intro name present
    simp only [Expr.leaves,arity,List.ofFn_zero,List.flatten_nil,List.not_mem_nil] at present

/-- Source-key scope and hole closure extract the finite Trace witness for
the scalar case. This is a concrete exposure-elimination branch. -/
theorem scalar_trace
    (inside : Fragment (inspect state (.scalar base) bounds (some root)) report)
    (valid : ∀ model, models model → ProjectionModels state report model)
    (known : GeneralNominalUniformInspectionInputs.Input models values state bounds (some root) (.leaf hole))
    (member : hole ∈ inventory.holes)
    (leafValues : ∀ model, models model → ∀ name ∈ inventory.holes, At model .actual (origins name) (values model name))
    (covered : GeneralDeclarationPatterns.covered pattern = true)
    (translated : translate context.state.constructors context.interpretation pattern = .scalar base)
    (scope : GeneralNominalSourceLabelVocabulary.Allowed keys (inventory.holes.erase hole) pattern) :
    GeneralNominalUniformHoleLabels.Labelled models context origins (inventory.holes.erase hole) (origins hole) pattern
      (.node (.scalar base) Fin.elim0) ∧
    ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
      (eliminate inventory hole (GeneralNominalPatternInventory.encode pattern) extra) 1 :=
  ⟨scalar_replacement inside valid known member leafValues covered translated,
    GeneralNominalSourceLabelVocabulary.replacement_trace inventory member scope⟩

/-- A scalar event needs no supplied child readback, numeric budget, or
replacement-variable scope. All three follow from its original source query. -/
theorem scalar_source_trace
    (source : SourceQuery context sources (.scalar base))
    (scope : ∀ pattern ∈ sources, GeneralNominalSourceLabelVocabulary.Scoped keys pattern)
    (inside : Fragment (inspect state (.scalar base) bounds (some root)) report)
    (valid : ∀ model, models model → ProjectionModels state report model)
    (known : GeneralNominalUniformInspectionInputs.Input models values state bounds (some root) (.leaf hole))
    (member : hole ∈ inventory.holes)
    (leafValues : ∀ model, models model → ∀ name ∈ inventory.holes, At model .actual (origins name) (values model name)) :
    ∃ pattern, GeneralNominalUniformHoleLabels.Labelled models context origins (inventory.holes.erase hole) (origins hole) pattern
      (.node (.scalar base) Fin.elim0) ∧
      ∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
        (eliminate inventory hole (GeneralNominalPatternInventory.encode pattern) extra) 1 := by
  obtain ⟨pattern,scope,covered,translated⟩ := source_query_scoped source scope
  exact ⟨pattern,scalar_trace inside valid known member leafValues covered translated (scalar_allowed scope translated)⟩

end Yulang.GeneralNominalExposureSources
