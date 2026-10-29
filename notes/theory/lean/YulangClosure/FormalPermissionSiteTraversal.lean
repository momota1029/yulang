import YulangClosure.FormalPermissionExportWitnessNative

/-! Concrete encoding of SourceAnnotationType/Value/EffectRow, with exactly
the Function/Tuple effect-visit recurrence of candidate_formal_value_pair.
Nat encodings of HIR identities/positions and extraction of the actual tree,
events, code and capture snapshot remain external correspondence obligations.
No generic child/effectPosition oracle, native authenticity axiom, or unequal
transport claim is introduced. The failed SourceTransport module is not used. -/
namespace YulangClosure.FormalPermissionSiteTraversal
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionExportWitness

structure SourceRow where
  position : Nat
  concrete : List Nat
  variables : List Nat
  deriving DecidableEq, Repr

inductive SourceLeaf where
  | unit | int | bool | str
  | variable (name : Nat)
  | hole (position : Nat)
  deriving DecidableEq, Repr

mutual
  /-- All actual value constructors; top effects are retained even when this
  constructor does not itself call candidate_formal_effect_port for them. -/
  inductive Annotation where
    | leaf (effects : Option SourceRow) (kind : SourceLeaf)
    | function (effects : Option SourceRow) (argument result : Annotation)
    | tuple (effects : Option SourceRow) (elements : Annotations)
  /-- Ordered Vec encoding, including empty input (successful formation must
  separately establish the source's nonempty-tuple requirement). -/
  inductive Annotations where
    | nil
    | cons (head : Annotation) (tail : Annotations)
end

def Annotation.effects : Annotation → Option SourceRow
  | .leaf effects _ => effects
  | .function effects _ _ => effects
  | .tuple effects _ => effects

def Annotations.get : Annotations → Nat → Option Annotation
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, n + 1 => tail.get n

/-- Concrete structural lookup, decreasing in the full path. A successful
lookup alone does not say the constructor visited that node's effect row. -/
def follow (tree : Annotation) : List Step → Option Annotation
  | [] => some tree
  | step :: rest =>
      match tree, step with
      | .function _ argument _, .argument => follow argument rest
      | .function _ _ result, .result => follow result rest
      | .tuple _ elements, .element index =>
          (elements.get index).bind (fun child => follow child rest)
      | _, _ => none

def effectAt (tree : Annotation) (path : List Step) : Option (Option SourceRow) :=
  (follow tree path).map Annotation.effects

/-- Exactly the source effect-call recurrence. Leaves emit no effect visit;
Function visits both immediate effect ports and all nested value children;
Tuple visits its ordered value children. None denotes an omitted row site.
The relation describes visitation, not chronological event order. -/
inductive EffectVisit : Annotation → List Step → Option SourceRow → Prop where
  | argument (effects : Option SourceRow) (a r : Annotation) :
      EffectVisit (.function effects a r) [.argument] a.effects
  | result (effects : Option SourceRow) (a r : Annotation) :
      EffectVisit (.function effects a r) [.result] r.effects
  | inArgument {a : Annotation} {path : List Step} {row : Option SourceRow}
      (effects : Option SourceRow) (r : Annotation) (child : EffectVisit a path row) :
      EffectVisit (.function effects a r) (.argument :: path) row
  | inResult {r : Annotation} {path : List Step} {row : Option SourceRow}
      (effects : Option SourceRow) (a : Annotation) (child : EffectVisit r path row) :
      EffectVisit (.function effects a r) (.result :: path) row
  | inElement {elements : Annotations} {index : Nat} {child : Annotation}
      {path : List Step} {row : Option SourceRow} (effects : Option SourceRow)
      (found : elements.get index = some child) (nested : EffectVisit child path row) :
      EffectVisit (.tuple effects elements) (.element index :: path) row

theorem visit_nonempty {tree : Annotation} {path : List Step} {row : Option SourceRow}
    (visit : EffectVisit tree path row) : path ≠ [] := by
  cases visit <;> simp

/-- Soundness of every concrete traversal constructor under full path lookup. -/
theorem visit_lookup {tree : Annotation} {path : List Step} {row : Option SourceRow}
    (visit : EffectVisit tree path row) : effectAt tree path = some row := by
  induction visit with
  | argument => rfl
  | result => rfl
  | inArgument effects r child ih => exact ih
  | inResult effects a child ih => exact ih
  | inElement effects found nested ih =>
      simpa only [effectAt, follow, found, Option.bind_some] using ih

/-- One full structural path cannot denote two different nested effect rows,
including all concrete operands/symbolic variables, or omitted vs explicit. -/
theorem visit_unique {tree : Annotation} {path : List Step}
    {first second : Option SourceRow}
    (a : EffectVisit tree path first) (b : EffectVisit tree path second) :
    first = second := by
  have left := visit_lookup a
  have right := visit_lookup b
  rw [left] at right
  exact Option.some.inj right

theorem leaf_has_no_visits (effects : Option SourceRow) (kind : SourceLeaf)
    (path : List Step) (row : Option SourceRow) :
    ¬ EffectVisit (.leaf effects kind) path row := by
  intro impossible
  cases impossible

theorem tuple_element_lookup (effects : Option SourceRow) (elements : Annotations)
    (index : Nat) (child : Annotation) (rest : List Step)
    (found : elements.get index = some child) :
    follow (.tuple effects elements) (.element index :: rest) = follow child rest := by
  simp only [follow, found, Option.bind_some]

structure Site where
  context : Context
  enclosingAnnotation : Nat
  path : List Step
  row : SourceRow
  deriving DecidableEq, Repr

def Associated (context : Context) (annotationPosition : Nat)
    (tree : Annotation) (site : Site) : Prop :=
  site.context = context ∧ site.enclosingAnnotation = annotationPosition ∧
    EffectVisit tree site.path (some site.row)

theorem associated_row_unique {context : Context} {annotationPosition : Nat}
    {tree : Annotation} {first second : Site}
    (a : Associated context annotationPosition tree first)
    (b : Associated context annotationPosition tree second)
    (samePath : first.path = second.path) : first.row = second.row := by
  have firstVisit := a.2.2
  rw [samePath] at firstVisit
  exact Option.some.inj (visit_unique firstVisit b.2.2)

theorem different_paths_distinct (first second : Site)
    (different : first.path ≠ second.path) : first ≠ second := by
  intro same
  exact different (congrArg Site.path same)

/-- Both coordinates survive, including when numerically different. No
position equality is inferred from the same annotation owner or occurrence. -/
theorem associate_visit (context : Context) (enclosingPosition : Nat)
    (tree : Annotation) (path : List Step) (row : SourceRow)
    (visit : EffectVisit tree path (some row)) :
    Associated context enclosingPosition tree ⟨context, enclosingPosition, path, row⟩ :=
  ⟨rfl, rfl, visit⟩

/-- Conditional connection to the accepted export decoder. Native extraction
must supply BOTH the representative equation and independently materialized
node lookup; agreement between two output records is insufficient. -/
theorem identity_expected (context : Context) (snapshot : CaptureSnapshot)
    (lineage : Nat) (entry : Retained) (node : Nat)
    (identity : representative snapshot entry.allocatedRow = entry.allocatedRow)
    (materialized : nodeFor snapshot entry.allocatedRow = some node) :
    expected context snapshot lineage entry = some
      ⟨lineage, .definition context.owner, entry.metadata, entry.path,
       entry.allocatedRow, entry.allocatedRow, false, snapshot.capture,
       snapshot.root, node, node⟩ := by
  simp [expected, identity, materialized]

/-- No native tree/code/capture authenticity is inferred from record checks.
The exact successful constructor decode and entire observation list remain
explicit extraction premises until a frozen ordinary-source receipt supplies
their actual instance. -/
theorem identity_observations_decode (context : Context) (s : State)
    (code : ValueCode) (out : ValueDecoded context false s)
    (snapshot : CaptureSnapshot) (observations : List Observation)
    (decoded : decodeValue context false s code = some out)
    (allEntries : expectedAll context snapshot 0 out.entries = some observations) :
    decodeObserved context s code snapshot observations = some out := by
  have checked : observationsMatch context snapshot out.entries observations = true :=
    (observations_match_iff _ _ _ _).mpr allEntries
  simp [decodeObserved, decoded, checked]

end YulangClosure.FormalPermissionSiteTraversal
