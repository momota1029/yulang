import Yulang.GeneralNominalLabelledOriginClosure

/-! Finite constructor vocabularies with retained source-key templates
reify open recipe trees. Filling a template uses one shared substitution and
does not choose a catalogue key from a semantic nominal name. -/
namespace Yulang.GeneralNominalScopedRecipeLabels
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalOpenPatternLabels GeneralNominalSourceLabelVocabulary GeneralNominalHoleElimination
open GeneralPatternVariableProvenance GeneralNominalReadbackFunctionality

variable {tests : List Test} {keys remaining : List Nat}
variable {allowed surviving : Nat → Prop} {substitution : Nat → Pattern}

mutual
  theorem subst_uses (pattern : Pattern) (known : Uses allowed pattern)
      (images : ∀ name, allowed name → Uses surviving (substitution name)) :
      Uses surviving (pattern.subst substitution) := by
    cases pattern with
    | var name => exact images name (known name (List.mem_singleton_self _))
    | app key arguments => exact args_subst_uses arguments known images
    | record key first last | join first last =>
      intro name member
      rcases List.mem_append.mp member with one | two
      · exact subst_uses first (fun n h => known n (List.mem_append_left _ h)) images name one
      · exact subst_uses last (fun n h => known n (List.mem_append_right _ h)) images name two
    | variant tag payload => exact subst_uses payload known images
  theorem args_subst_uses (patterns : List Pattern)
      (known : ∀ name ∈ variablesArgs patterns, allowed name)
      (images : ∀ name, allowed name → Uses surviving (substitution name)) :
      ∀ name ∈ variablesArgs (substArgs substitution patterns), surviving name := by
    cases patterns with
    | nil => intro name impossible; cases impossible
    | cons first last =>
      intro name member
      rcases List.mem_append.mp member with one | two
      · exact subst_uses first (fun n h => known n (List.mem_append_left _ h)) images name one
      · exact args_subst_uses last (fun n h => known n (List.mem_append_right _ h)) images name two
end

def Vocabulary (tests : List Test) : Expr α → Prop
  | .leaf _ => True
  | .node test children => test ∈ tests ∧ ∀ position, Vocabulary tests (children position)

theorem vocabulary_bind {substitution : α → Expr β} (known : Vocabulary tests term)
    (images : ∀ name ∈ term.leaves, Vocabulary tests (substitution name)) :
    Vocabulary tests (term.bind substitution) := by
  induction term with
  | leaf name => exact images name (List.mem_singleton_self _)
  | node test children ih =>
    exact ⟨known.1,fun i => ih i (known.2 i) (fun name member => images name
      (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,member⟩))⟩

theorem recipe_vocabulary (recipe : Recipe body root term)
    (known : ∀ entry ∈ body.tests, entry.2 ∈ tests) : Vocabulary tests term := by
  induction recipe with
  | capture => trivial
  | node root test children member recipes ih => exact ⟨known _ member,ih⟩

/-- Each template retains a source key and has one distinct leaf per actual
constructor position. Source extraction of these finite templates is a
syntactic producer obligation, separate from semantic output readback. -/
def NodeTemplates (context : GeneralNominalCandidates.Context) (keys : List Nat) (tests : List Test) : Prop :=
  ∀ test ∈ tests, TestCanonical test → ∃ pattern,
    Label context pattern (.node test (fun position => .leaf position.val)) ∧ Scoped keys pattern ∧
      Uses (fun name => name < arity test) pattern

theorem reify (templates : NodeTemplates context keys tests) (term : Expr Nat)
    (known : Vocabulary tests term) (canonical : Canonical term) (closed : Closed remaining term) :
    ∃ pattern, Label context pattern term ∧ Allowed keys remaining pattern := by
  classical
  induction term with
  | leaf name =>
    exact ⟨.var name,⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩,
      .var _,by intro n member; cases List.mem_singleton.mp member; exact closed name (List.mem_singleton_self _)⟩
  | node test children ih =>
    obtain ⟨pattern,label,scope,used⟩ := templates test known.1 canonical.1
    have each : ∀ position, ∃ pattern, Label context pattern (children position) ∧ Allowed keys remaining pattern :=
      fun position => ih position (known.2 position) (canonical.2 position)
        (GeneralNominalOpenCaptureLabels.child_closed closed position)
    let chosen : Fin (arity test) → Pattern := fun i => Classical.choose (each i)
    have chosenLabel (i) : Label context (chosen i) (children i) := (Classical.choose_spec (each i)).1
    have chosenScope (i) : Allowed keys remaining (chosen i) := (Classical.choose_spec (each i)).2
    let capture : Nat → Pattern := fun name => if h : name < arity test then chosen ⟨name,h⟩ else .var name
    let trees : Nat → Expr Nat := fun name => if h : name < arity test then children ⟨name,h⟩ else .leaf name
    have images (name) : Label context (capture name) (trees name) := by
      by_cases small : name < arity test
      · simpa only [capture,trees,dite_eq_left small] using chosenLabel ⟨name,small⟩
      · simp only [capture,trees,dite_eq_right small]
        exact ⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩
    have imageScope (name) : Scoped keys (capture name) := by
      by_cases small : name < arity test
      · simpa only [capture,dite_eq_left small] using (chosenScope ⟨name,small⟩).1
      · simp only [capture,dite_eq_right small]; exact .var _
    refine ⟨normalize (pattern.subst capture),?_,?_,?_⟩
    · have filled := filled_label label capture trees images
      have equal : (Expr.node test (fun position => Expr.leaf position.val)).bind trees = .node test children := by
        simp only [Expr.bind]
        congr 1
        funext position
        simp only [trees,dite_eq_left position.isLt]
      exact equal ▸ filled
    · exact normalized_subst_scoped label.1 scope capture imageScope (fun name => (images name).1)
    · apply normalize_uses
      exact subst_uses pattern used (fun name small => by
        simpa only [capture,dite_eq_left small] using (chosenScope ⟨name,small⟩).2)

theorem recipe_label (templates : NodeTemplates context keys tests)
    (recipe : Recipe body root term)
    (vocabulary : ∀ entry ∈ body.tests, entry.2 ∈ tests)
    (canonical : ∀ entry ∈ body.tests, TestCanonical entry.2) :
    ∃ pattern, Label context pattern term ∧ Allowed keys (body.variables.map GeneralNominalMaterialization.Use.name) pattern :=
  reify templates term (recipe_vocabulary recipe vocabulary)
    (GeneralNominalIndexedOutputProduction.recipe_canonical recipe canonical) (by
      intro name member
      obtain ⟨whereUsed,used⟩ := recipe_leaf_use recipe member
      exact List.mem_map.mpr ⟨_,used,rfl⟩)

end Yulang.GeneralNominalScopedRecipeLabels
