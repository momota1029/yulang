import Yulang.GeneralNominalSourceLabelVocabulary

/-! Uniform actual meanings give indexed readbacks, and shared actual origins
give one source-labelled substitution outside the model quantifier. Semantic
sharing does not assert a common subterm-size presentation. -/
namespace Yulang.GeneralNominalUniformCaptureProduction
open GeneralDeclarationPatterns GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalReadbackFunctionality GeneralNominalFiniteMeaning GeneralNominalIndexedHoleReadback
open GeneralNominalHoleElimination GeneralNominalOpenPatternLabels GeneralNominalUniformHoleLabels
open GeneralNominalUniformReportDispatch

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty}
variable {origins : Nat → Origin} {allowed : Pattern → Prop}

theorem meaning_holds (term : Expr Nat) (canonical : Canonical term)
    (meaning : At model .actual root (denote valuation term))
    (leaves : ∀ name ∈ term.leaves, At model .actual (origins name) (valuation name)) :
    Holds model (interpret origins term) root := by
  induction term generalizing root with
  | leaf name =>
    have leaf := leaves name (List.mem_singleton_self _)
    refine ⟨meaning.1,leaf.1,?_⟩
    intro first last one two
    exact ⟨CommonNominalFullCarrier.subtype_trans (meaning.2 first one).1 (leaf.2 last two).2,
      CommonNominalFullCarrier.subtype_trans (leaf.2 last two).1 (meaning.2 first one).2⟩
  | node test children ih =>
    refine ⟨⟨meaning.1,?_⟩,?_⟩
    · intro actual seen
      have equal := meaning.2 actual seen
      cases test with
      | scalar base => exact equal
      | structural shape => exact ⟨List.ofFn (fun i => denote valuation (children i)),List.length_ofFn ..,equal⟩
      | nominal name count => exact ⟨List.ofFn (fun i => Sum.inl (denote valuation (children i))),List.length_ofFn ..,equal⟩
    · intro position
      apply ih position (canonical.2 position) (project_value test canonical.1 _ meaning position)
      intro name member
      exact leaves name (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨position,rfl⟩,member⟩)

theorem input_readback
    (leafValues : ∀ model, models model → ∀ name ∈ remaining, At model .actual (origins name) (values model name))
    (known : GeneralNominalUniformInspectionInputs.Input models values state bounds (some root) term)
    (closed : Closed remaining term) : Readback models origins remaining root term := by
  refine ⟨?_,closed⟩
  intro model valid
  exact meaning_holds term (known model valid).1 ((known model valid).2.2 root rfl)
    (fun name member => leafValues model valid name (closed name member))

/-- This choice is uniform: the pattern/tree pair is selected before any
model is supplied. Actual-origin sharing then transports it to all uses. -/
theorem shared_candidate
    (leafValues : ∀ model, models model → ∀ name ∈ remaining, At model .actual (origins name) (values model name))
    (captured : Captures context remaining allowed models values report)
    (present : entry ∈ report.captures) (recorded : entry.origin = some actual)
    (shared : ∀ model, models model → Same model actual representative) :
    ∃ pattern term, Sourced context remaining allowed pattern term ∧
      Readback models origins remaining representative term := by
  obtain ⟨pattern,term,source,known⟩ := captured entry present
  rw [recorded] at known
  exact ⟨pattern,term,source,alias (input_readback leafValues known source.2.1) shared⟩

theorem simultaneous (names : List Nat) (representatives : Nat → Origin)
    (leafValues : ∀ model, models model → ∀ name ∈ remaining, At model .actual (origins name) (values model name))
    (captured : Captures context remaining allowed models values report)
    (coverage : ∀ name ∈ names, ∃ entry ∈ report.captures, entry.name = name ∧ ∃ actual,
      entry.origin = some actual ∧ ∀ model, models model → Same model actual (representatives name)) :
    ∃ substitution : Nat → Pattern, ∃ terms : Nat → Expr Nat,
      (∀ name, Label context (substitution name) (terms name)) ∧
      (∀ name ∉ names, substitution name = .var name ∧ terms name = .leaf name) ∧
      ∀ name ∈ names, Sourced context remaining allowed (substitution name) (terms name) ∧
        Readback models origins remaining (representatives name) (terms name) := by
  classical
  have witnesses : ∀ name ∈ names, ∃ pair : Pattern × Expr Nat,
      Sourced context remaining allowed pair.1 pair.2 ∧ Readback models origins remaining (representatives name) pair.2 := by
    intro name member
    obtain ⟨entry,present,identical,actual,recorded,shared⟩ := coverage name member
    obtain ⟨pattern,term,source,readback⟩ := shared_candidate leafValues captured present recorded shared
    exact ⟨(pattern,term),source,readback⟩
  let pair : Nat → Pattern × Expr Nat := fun name => if member : name ∈ names then
    Classical.choose (witnesses name member) else (.var name,.leaf name)
  refine ⟨fun name => (pair name).1,fun name => (pair name).2,?_,?_,?_⟩
  · intro name
    by_cases member : name ∈ names
    · simpa only [pair,dite_eq_left member] using (Classical.choose_spec (witnesses name member)).1.1
    · simp only [pair,dite_eq_right member]
      exact ⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩
  · intro name missing
    simp only [pair,dite_eq_right missing,and_self]
  · intro name member
    simpa only [pair,dite_eq_left member] using Classical.choose_spec (witnesses name member)

/-- A supplied fixed source name has its actual valuation in every model;
remaining source holes may denote recursive types and need not be ground. -/
theorem source_leaf_values (identities : Nat → Nat) :
    ∀ model : GeneralNominalCommonBridge.Assignment, ∀ name,
      At model .actual (.source (identities name)) (model (identities name)).1 := by
  intro model name
  refine ⟨⟨_,.source _⟩,?_⟩
  intro actual seen
  cases seen
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

def neededNames (packet : GeneralNominalSaturationState.Packet roles) : List Nat :=
  packet.declaration.requirements.flatMap fun clause => variablesArgs (normalizeArgs clause.arguments)

theorem needed_names (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalSharedCaptures.Needed packet name ↔ name ∈ neededNames packet := by
  exact List.mem_flatMap.symm

/-- Uniform full-report captures produce the simultaneous substitution used
by real child emission. Positive shared-origin evidence supplies each needed
name; semantic agreement alone is not used as a tree-size comparison. -/
theorem packet_substitution (packet : GeneralNominalSaturationState.Packet roles)
    (generation : GeneralNominalSharedCaptures.GenerationGuard tracked packet)
    (branch : ∀ model, models model → packet.Holds model)
    (captured : Captures context remaining allowed models values
      (GeneralNominalSharedCaptures.inheritedReport packet)) :
    ∃ substitution : Nat → Pattern, ∃ terms : Nat → Expr Nat,
      (∀ name, Label context (substitution name) (terms name)) ∧
      (∀ name, ¬ GeneralNominalSharedCaptures.Needed packet name →
        substitution name = .var name ∧ terms name = .leaf name) ∧
      (∀ name, GeneralNominalSharedCaptures.Needed packet name →
        Closed remaining (terms name) ∧ allowed (substitution name)) ∧
      ∀ model, models model → ∀ name, GeneralNominalSharedCaptures.Needed packet name →
        GeneralNominalStructuralContainment.CaptureValue packet model name (denote (values model) (terms name)) := by
  classical
  have candidates : ∀ name, GeneralNominalSharedCaptures.Needed packet name →
      ∃ pair : Pattern × Expr Nat,
        Sourced context remaining allowed pair.1 pair.2 ∧
        ∀ model, models model → GeneralNominalStructuralContainment.CaptureValue packet model name
          (denote (values model) pair.2) := by
    intro name needed
    obtain ⟨representative,usable⟩ := generation name needed
    obtain ⟨entry,member,same,recorded⟩ := usable.1.1
    obtain ⟨pattern,term,source,known⟩ := captured entry member
    refine ⟨(pattern,term),source,?_⟩
    intro model valid
    apply GeneralNominalOpenCaptureLabels.shared_capture_value packet (branch model valid) generation needed
    refine ⟨entry.bounds,entry.origin,?_,known model valid⟩
    cases entry
    cases same
    exact member
  let chosen : Nat → Pattern × Expr Nat := fun name =>
    if used : GeneralNominalSharedCaptures.Needed packet name then
      Classical.choose (candidates name used) else (.var name,.leaf name)
  refine ⟨fun name => (chosen name).1,fun name => (chosen name).2,?_,?_,?_,?_⟩
  · intro name
    by_cases used : GeneralNominalSharedCaptures.Needed packet name
    · simpa only [chosen,dite_eq_left used] using (Classical.choose_spec (candidates name used)).1.1
    · simp only [chosen,dite_eq_right used]
      exact ⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩
  · intro name unused
    simp only [chosen,dite_eq_right unused,and_self]
  · intro name used
    simpa only [chosen,dite_eq_left used] using (Classical.choose_spec (candidates name used)).1.2
  · intro model valid name used
    simpa only [chosen,dite_eq_left used] using (Classical.choose_spec (candidates name used)).2 model valid

end Yulang.GeneralNominalUniformCaptureProduction
