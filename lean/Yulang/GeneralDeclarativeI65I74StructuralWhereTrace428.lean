import Yulang.GeneralDeclarativeI65I74StructuralWhereForest427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open I72 (Event SourcePrimitives SourceTrace WhereForest SupportForest)
open CommonRoleOutermostResolver (Tree Dictionary Result Summarizes All₂)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarations (DeclarationChecked)

private def leafPlace428 : Placement := ⟨fun _ _ => point 0, fun _ _ => 0⟩

def leafFrame428 {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {k}
    (a : ReviewedWhereAt427 f k) : AuthoredBodyFrame393 s.core a.original.child :=
  let h := a.actual.positive
  ⟨h.ordinal,h.decl,h.fromRegistry,h.visibleDecl,leafPlace428,h.capture⟩

def leafEvent428 {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {k}
    (a : ReviewedWhereAt427 f k) : Event s a.original.child :=
  originalNoOutputEvent427 s.b6 (leafFrame428 a) a.actual.positive.head a.noOutputs

theorem leaf_event_no_where428 {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {k}
    (a : ReviewedWhereAt427 f k) : (leafEvent428 a).kids = [] := by
  simp [leafEvent428,leafFrame428,originalNoOutputEvent427,I72.Event.kids,
    frameWhereKids400,children,AuthoredBodyFrame393.clauses,a.leaf]

def parentEvent428 {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q}
    (a : OriginalPreparedRoot427 f) (empty : q.demand.outputs = []) : Event s q :=
  originalNoOutputEvent427 s.b6 f (a.declaration ▸ a.visiblePoint.positive.head) empty

/-- Only *local* primitive election is a premise of this adapter.
Neither a result, a classified child, a semantic dictionary nor a model
can be passed as a substitute. In particular this interface is not an
installation into any official rule system. -/
def WhereLocal428 (R : SourcePrimitives) (s : I72.State) (q : Request)
    (f : AuthoredBodyFrame393 s.core q) : Prop :=
  ∀ k (a : ReviewedWhereAt427 f k), R.elected s a.original.child (leafEvent428 a) []

def leafTree428 {s : State} {q : Request} {f : AuthoredBodyFrame393 s q} {k}
    (a : ReviewedWhereAt427 f k) : Tree :=
  .selected a.actual.positive.decl.id []

def whereTrees428 {s : State} {q : Request} {f : AuthoredBodyFrame393 s q} {ks}
    (v : ReviewedForest427 f ks) : List Tree :=
  match v with
  | .nil => []
  | .cons a tail => leafTree428 a :: whereTrees428 tail

def replayLeaf428 {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (localPick : WhereLocal428 R s q f)
    {k} (a : ReviewedWhereAt427 f k) :
    SourceTrace R s a.original.child (leafTree428 a) (some (leafEvent428 a)) :=
  let e := leafEvent428 a
  .selected e (a.actual.positive.safe s.b6) (localPick k a) .nil
    ((leaf_event_no_where428 a).symm ▸ .nil)

/-- Each list node comes from the independently verified original
entry. The selected child is not an assumed proof or dictionary. -/
def replayWhere428 {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (localPick : WhereLocal428 R s q f)
    {ks} (v : ReviewedForest427 f ks) : WhereForest R s v.requests (whereTrees428 v) :=
  match v with
  | .nil => .nil
  | .cons a tail => .cons (replayLeaf428 localPick a) (replayWhere428 localPick tail)

/-- The path points into an actual WhereForest derivation, not into a
list of returned declaration IDs or a list of expected child requests.
The stored event is the one at the chosen trace node. -/
inductive SelectedAt428 (R : SourcePrimitives) (s : I72.State) :
    {qs : List Request} → {ts : List Tree} → WhereForest R s qs ts →
      Nat → (q : Request) → Event s q → Prop where
  | here {q : Request} {e : Event s q} {t qs ts}
      (a : SourceTrace R s q t (some e)) (rest : WhereForest R s qs ts) :
      SelectedAt428 R s (.cons a rest) 0 q e
  | there {q x : Request} {e : Event s x} {t ev qs ts n}
      (a : SourceTrace R s q t ev) {rest : WhereForest R s qs ts} :
      SelectedAt428 R s rest n x e → SelectedAt428 R s (.cons a rest) (n+1) x e

theorem named_selected_leaf_uses_literal_ordinal_and_actual_event428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (localPick : WhereLocal428 R s q f)
    {ks} (v : ReviewedForest427 f ks) {i k : Nat}
    (atOrdinal : ks[i]? = some k) :
    ∃ leaf : ReviewedWhereAt427 f k,
      SelectedAt428 R s (replayWhere428 localPick v) i
          leaf.original.child (leafEvent428 leaf) ∧
      leaf.original.child.occurrence = q.occurrence ++ [k] ∧
      (leafEvent428 leaf).frame.decl = leaf.actual.positive.decl ∧
      s.core.current.ordinary.equations[leaf.original.rowOrdinal]? =
        some (writtenRow427 f leaf.original.name leaf.original.label leaf.original.binder) := by
  induction v generalizing i k with
  | nil => simp at atOrdinal
  | @cons j js a rest ih =>
    cases i with
    | zero =>
      have same : j = k := by simpa using atOrdinal
      subst k
      exact ⟨a,.here (replayLeaf428 localPick a) (replayWhere428 localPick rest),
        rfl,rfl,a.original.retained⟩
    | succ n =>
      obtain ⟨leaf,entered,occ,decl,retained⟩ := ih (by simpa using atOrdinal)
      exact ⟨leaf,.there (replayLeaf428 localPick a) entered,occ,decl,retained⟩

theorem checked_parent_uses_actual_lexical_capture428
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q}
    (p : OriginalPreparedRoot427 f) (checked : DeclarationChecked
      (authoredRegistry s.core.current).constructors (authoredRegistry s.core.current).roles f.decl)
    {k} (arg : OriginalRecordArgument427 f k 0) :
    f.names.input arg.binder = p.visiblePoint.positive.capture arg.binder := by
  unfold AuthoredBodyFrame393.names GeneralDeclarativeFrameReadback325.sourceNames
  exact (GeneralDeclarativeProducedNames325.exact_input checked arg.inHead).trans
    (p.lexical _ arg.inHead)

def parentWhere428 {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (root : OriginalPreparedRoot427 f)
    (empty : q.demand.outputs = []) (localPick : WhereLocal428 R s q f)
    (v : ReviewedForest427 f (List.range f.decl.requirements.length)) :
    WhereForest R s (parentEvent428 root empty).kids (whereTrees428 v) :=
  show WhereForest R s (frameWhereKids400 f) (whereTrees428 v) from
    (reviewed_source_order_is_entire_original_where427 v) ▸ replayWhere428 localPick v

/-- Install no global rule: this constructs the real named finite
derivation relative to independently supplied local primitives and
uses no support output, reordering, or pre-classified child. -/
def parentTrace428 {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (root : OriginalPreparedRoot427 f)
    (empty : q.demand.outputs = [])
    (parentPick : R.elected s q (parentEvent428 root empty) [])
    (localPick : WhereLocal428 R s q f)
    (v : ReviewedForest427 f (List.range f.decl.requirements.length)) :
    SourceTrace R s q (.selected f.decl.id (whereTrees428 v)) (some (parentEvent428 root empty)) :=
  .selected (parentEvent428 root empty) (root.visiblePoint.positive.safe s.b6) parentPick .nil
    (parentWhere428 root empty localPick v)


theorem SelectedAt428.requests {R : SourcePrimitives} {s : I72.State}
    {qs ts} {forest : WhereForest R s qs ts} {i q e}
    (h : SelectedAt428 R s forest i q e) : qs[i]? = some q := by
  induction h with
  | here => rfl
  | there _ _ ih => simpa using ih

private theorem selection_survives_request_cast428 {R : SourcePrimitives} {s : I72.State}
    {qs us ts} (aligned : qs = us) (forest : WhereForest R s qs ts) {i q e}
    (original : SelectedAt428 R s forest i q e) :
    SelectedAt428 R s (aligned ▸ forest) i q e := by
  cases aligned
  exact original

def TraceChild428 {R : SourcePrimitives} {s : I72.State} {q t ev}
    (trace : SourceTrace R s q t ev) (i : Nat) (child : Request) (e : Event s child) : Prop :=
  match trace with
  | .selected _ _ _ _ forest => SelectedAt428 R s forest i child e
  | .rootK2 _ | .other _ _ _ _ => False

/-- Formal link to the actual child of the actual named selected
parent trace. The existential is populated by the exact original
where row at this ordinal, not by equality of dictionary or value. -/
theorem original_where_position_is_actual_selected_trace_child428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (p : OriginalPreparedRoot427 f)
    (checked : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles f.decl)
    (empty : q.demand.outputs = []) (parentPick : R.elected s q (parentEvent428 p empty) [])
    (localPick : WhereLocal428 R s q f)
    (v : ReviewedForest427 f (List.range f.decl.requirements.length))
    (i : Fin f.decl.requirements.length) :
    ∃ a : ReviewedWhereAt427 f i.val,
      TraceChild428 (parentTrace428 p empty parentPick localPick v) i.val
        a.original.child (leafEvent428 a) ∧
      (parentEvent428 p empty).kids[i.val]? = some a.original.child ∧
      a.original.child.occurrence = q.occurrence ++ [i.val] ∧
      (leafEvent428 a).frame.decl = a.actual.positive.decl ∧
      f.names.input a.original.binder = p.visiblePoint.positive.capture a.original.binder ∧
      s.core.current.ordinary.equations[a.original.rowOrdinal]? =
        some (writtenRow427 f a.original.name a.original.label a.original.binder) := by
  have atIndex : (List.range f.decl.requirements.length)[i.val]? = some i.val :=
    List.getElem?_range i.isLt
  obtain ⟨a,position,occ,decl,retained⟩ :=
    named_selected_leaf_uses_literal_ordinal_and_actual_event428 localPick v atIndex
  have attached : SelectedAt428 R s (parentWhere428 p empty localPick v) i.val
      a.original.child (leafEvent428 a) :=
    selection_survives_request_cast428 (reviewed_source_order_is_entire_original_where427 v)
      (replayWhere428 localPick v) position
  exact ⟨a,attached,attached.requests,occ,decl,checked_parent_uses_actual_lexical_capture428 p checked a.original,
    retained⟩

theorem actual_where_children_summarize_in_their_source_order428
    {s : State} {q : Request} {f : AuthoredBodyFrame393 s q} {ks}
    (v : ReviewedForest427 f ks) :
    All₂ Summarizes (whereTrees428 v) (v.dictionaries.map Result.selected) := by
  induction v with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (.selected .nil (.selected rfl)) ih

theorem actual_named_tree_has_exact_source_ordered_dictionary428
    {s : State} {q : Request} {f : AuthoredBodyFrame393 s q} {ks}
    (v : ReviewedForest427 f ks) :
    Summarizes (.selected f.decl.id (whereTrees428 v)) (.selected (.node f.decl.id v.dictionaries)) :=
  .selected (actual_where_children_summarize_in_their_source_order428 v) (.selected rfl)

end Yulang.GeneralDeclarativeI65.StructuralWhere428
