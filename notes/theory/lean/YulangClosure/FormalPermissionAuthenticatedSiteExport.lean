import YulangClosure.FormalPermissionSiteTraversal

/-! Source-tree traversal versus actual constructor Effect-port visitation.
The source traversal includes the root and every optional row. The constructor
visits only paths ending in a Function argument/result edge: top-level rows
and bare Tuple-element rows are not Effect-port calls. Native extraction of
the executing HIR/action, code, events and capture snapshot remains OPEN.
No native instance or snapshot authenticity is inferred from these relations. -/
namespace YulangClosure.FormalPermissionAuthenticatedSiteExport
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionExportWitness FormalPermissionSiteTraversal

/-- Independent traversal of EVERY type node, including root/omitted rows.
These constructors encode the actual SourceAnnotationValue tree rather than
accepting a generic child/effect-position oracle. -/
inductive SourceTreeVisit : Annotation → List Step → Option SourceRow → Prop where
  | root (tree : Annotation) : SourceTreeVisit tree [] tree.effects
  | inArgument {a : Annotation} {path : List Step} {row : Option SourceRow}
      (effects : Option SourceRow) (r : Annotation)
      (nested : SourceTreeVisit a path row) :
      SourceTreeVisit (.function effects a r) (.argument :: path) row
  | inResult {r : Annotation} {path : List Step} {row : Option SourceRow}
      (effects : Option SourceRow) (a : Annotation)
      (nested : SourceTreeVisit r path row) :
      SourceTreeVisit (.function effects a r) (.result :: path) row
  | inElement {elements : Annotations} {index : Nat} {child : Annotation}
      {path : List Step} {row : Option SourceRow} (effects : Option SourceRow)
      (found : elements.get index = some child)
      (nested : SourceTreeVisit child path row) :
      SourceTreeVisit (.tuple effects elements) (.element index :: path) row

/-- Full paths ending in an actual Function Effect-port edge. Prefixes retain
all enclosing Function/Tuple nodes. The empty path never supplies a port. -/
inductive PortPath : List Step → Prop where
  | argument : PortPath [.argument]
  | result : PortPath [.result]
  | prepend (step : Step) {path : List Step} (rest : PortPath path) :
      PortPath (step :: path)

theorem port_path_nonempty {path : List Step} (port : PortPath path) : path ≠ [] := by
  cases port <;> simp

theorem source_visit_lookup {tree : Annotation} {path : List Step}
    {row : Option SourceRow} (visit : SourceTreeVisit tree path row) :
    effectAt tree path = some row := by
  induction visit with
  | root => rfl
  | inArgument effects r nested ih => exact ih
  | inResult effects a nested ih => exact ih
  | inElement effects found nested ih =>
      simpa only [effectAt, follow, found, Option.bind_some] using ih

theorem source_visit_unique {tree : Annotation} {path : List Step}
    {first second : Option SourceRow}
    (a : SourceTreeVisit tree path first) (b : SourceTreeVisit tree path second) :
    first = second := by
  have left := source_visit_lookup a
  have right := source_visit_lookup b
  rw [left] at right
  exact Option.some.inj right

theorem constructor_to_source {tree : Annotation} {path : List Step}
    {row : Option SourceRow} (visit : EffectVisit tree path row) :
    SourceTreeVisit tree path row ∧ PortPath path := by
  induction visit with
  | argument effects a r =>
      exact ⟨.inArgument effects r (.root a), .argument⟩
  | result effects a r =>
      exact ⟨.inResult effects a (.root r), .result⟩
  | inArgument effects r nested ih =>
      exact ⟨.inArgument effects r ih.1, .prepend .argument ih.2⟩
  | inResult effects a nested ih =>
      exact ⟨.inResult effects a ih.1, .prepend .result ih.2⟩
  | inElement effects found nested ih =>
      exact ⟨.inElement effects found ih.1, .prepend (.element _) ih.2⟩

theorem source_port_to_constructor {tree : Annotation} {path : List Step}
    {row : Option SourceRow} (visit : SourceTreeVisit tree path row)
    (port : PortPath path) : EffectVisit tree path row := by
  revert port
  induction visit with
  | root tree => intro port; cases port
  | inArgument effects r nested ih =>
      intro port
      cases port with
      | argument => cases nested; exact .argument effects _ r
      | prepend step rest => exact .inArgument effects r (ih rest)
  | inResult effects a nested ih =>
      intro port
      cases port with
      | result => cases nested; exact .result effects a _
      | prepend step rest => exact .inResult effects a (ih rest)
  | inElement effects found nested ih =>
      intro port
      cases port with
      | prepend step rest => exact .inElement effects found (ih rest)

/-- Exact all-constructors equivalence, with omitted and explicit rows in the
same quantified statement. This is not yet extraction from Rust events. -/
theorem constructor_iff_source_port (tree : Annotation) (path : List Step)
    (row : Option SourceRow) :
    EffectVisit tree path row ↔ SourceTreeVisit tree path row ∧ PortPath path :=
  ⟨constructor_to_source, fun pair => source_port_to_constructor pair.1 pair.2⟩

theorem omitted_port_iff (tree : Annotation) (path : List Step) :
    EffectVisit tree path none ↔ SourceTreeVisit tree path none ∧ PortPath path :=
  constructor_iff_source_port tree path none

/-- The source inventory retains the root row, while the actual formal
constructor has no root Effect-port call, even for an explicit root row. -/
theorem root_row_separation (tree : Annotation) (row : Option SourceRow)
    (rootRow : tree.effects = row) :
    SourceTreeVisit tree [] row ∧ ¬ EffectVisit tree [] row := by
  constructor
  · rw [← rootRow]
    exact .root tree
  · intro visit
    exact visit_nonempty visit rfl

/-- A Tuple-element coordinate by itself is a source node, not a Function
Effect port. Nested Function ports below that element remain represented. -/
theorem bare_element_not_port (index : Nat) : ¬ PortPath [.element index] := by
  intro port
  cases port with
  | prepend step rest => cases rest

/-- Conditional parent-facing application. The unchanged decoder equations
are extraction premises, not assertions that a real snapshot was obtained.
No statement about native authenticity follows merely from a supplied list. -/
theorem extracted_port_and_export (context : Context) (tree : Annotation)
    (path : List Step) (row : Option SourceRow)
    (sourceVisit : SourceTreeVisit tree path row) (port : PortPath path)
    (s : State) (code : ValueCode) (out : ValueDecoded context false s)
    (snapshot : CaptureSnapshot) (observations : List Observation)
    (decoded : decodeValue context false s code = some out)
    (allEntries : expectedAll context snapshot 0 out.entries = some observations) :
    EffectVisit tree path row ∧
      decodeObserved context s code snapshot observations = some out :=
  ⟨source_port_to_constructor sourceVisit port,
   identity_observations_decode context s code out snapshot observations decoded allEntries⟩

end YulangClosure.FormalPermissionAuthenticatedSiteExport
