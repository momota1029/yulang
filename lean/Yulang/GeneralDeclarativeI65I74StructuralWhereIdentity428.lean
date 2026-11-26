import Yulang.GeneralDeclarativeI65I74StructuralWhereFold428

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open I72 (Event SourcePrimitives SourceTrace WhereForest)
open CommonRoleOutermostResolver (Tree)

theorem SelectedAt428.event_is_unique {R : SourcePrimitives} {s : I72.State}
    {qs ts} {forest : WhereForest R s qs ts} {i q e}
    (one : SelectedAt428 R s forest i q e) {other : Request} {also : Event s other}
    (two : SelectedAt428 R s forest i other also) : HEq e also := by
  induction one generalizing other with
  | here =>
    cases two
    rfl
  | there _ _ ih =>
    cases two with
    | there _ a => exact ih a

theorem TraceChild428.original_request {R : SourcePrimitives} {s : I72.State}
    {q : Request} {event : Event s q} {t i child e}
    {trace : SourceTrace R s q t (some event)}
    (h : TraceChild428 trace i child e) : event.kids[i]? = some child := by
  cases trace
  exact h.requests

theorem TraceChild428.original_event_is_unique {R : SourcePrimitives} {s : I72.State}
    {q : Request} {t ev} {trace : SourceTrace R s q t ev} {i x e}
    (one : TraceChild428 trace i x e) {y : Request} {e' : Event s y}
    (two : TraceChild428 trace i y e') : HEq e e' := by
  cases trace with
  | rootK2 => exact False.elim one
  | other => exact False.elim one
  | selected => exact SelectedAt428.event_is_unique one two

/-- A trace-child certificate cannot cross *original source positions*.
Two children are allowed to have the same selected ID, the same semantic
value, and even the same displayed dictionary subtree. Those facts
have no bearing on the occurrence inequality used here. -/
theorem actual_trace_child_cannot_move_to_other_literal_ordinal428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (root : OriginalPreparedRoot427 f)
    (empty : q.demand.outputs = []) (parentPick : R.elected s q (parentEvent428 root empty) [])
    (localPick : WhereLocal428 R s q f)
    (v : ReviewedForest427 f (List.range f.decl.requirements.length))
    {i j : Nat} (different : i ≠ j) {a : OriginalRecordArgument427 f i 0}
    {b : OriginalRecordArgument427 f j 0} {e : Event s b.child} :
    ¬ TraceChild428 (parentTrace428 root empty parentPick localPick v) i b.child e := by
  intro alleged
  have here := TraceChild428.original_request alleged
  have actual : (parentEvent428 root empty).kids[i]? = some a.child :=
    structural_where_keeps_original_child_at_ordinal427 a
  have swapped : a.child = b.child := Option.some.inj (actual.symm.trans here)
  exact different_original_clause_ordinals_have_different_child_occurrences427 a b different
    (congrArg Request.occurrence swapped)

/- A certificate inspection, not evaluation/search of a source
system. Mutual recursion inspects only actual finite trace subproofs.
Support dependencies and requested writes are counted separately. -/
mutual
def ZeroSupportSelected428 {R : SourcePrimitives} {s : I72.State} :
    {q : Request} → {t : Tree} → {ev : Option (Event s q)} →
      SourceTrace R s q t ev → Prop
  | q, _, _, .selected (needs := uses) _ _ _ _ xs =>
      uses = [] ∧ q.demand.outputs = [] ∧ ZeroSupportWhere428 xs
  | _, _, _, .rootK2 _ | _, _, _, .other _ _ _ _ => False

def ZeroSupportWhere428 {R : SourcePrimitives} {s : I72.State} :
    {qs : List Request} → {ts : List Tree} → WhereForest R s qs ts → Prop
  | _, _, .nil => True
  | _, _, .cons a xs => ZeroSupportSelected428 a ∧ ZeroSupportWhere428 xs
end

theorem replayed_original_leaf_has_no_support_or_outputs428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (localPick : WhereLocal428 R s q f)
    {k} (a : ReviewedWhereAt427 f k) :
    ZeroSupportSelected428 (replayLeaf428 localPick a) := by
  have cleared := leaf_event_no_where428 a
  unfold replayLeaf428
  change [] = [] ∧ a.original.child.demand.outputs = [] ∧ ZeroSupportWhere428 (cleared.symm ▸ (WhereForest.nil : WhereForest R s [] []))
  refine ⟨rfl,a.noOutputs,?_⟩
  generalize (leafEvent428 a).kids = qs at cleared ⊢
  cases cleared
  trivial

theorem replayed_original_where_has_no_support_or_outputs428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (localPick : WhereLocal428 R s q f)
    {ks} (v : ReviewedForest427 f ks) :
    ZeroSupportWhere428 (replayWhere428 localPick v) := by
  induction v with
  | nil => trivial
  | cons a tail ih =>
    exact ⟨replayed_original_leaf_has_no_support_or_outputs428 localPick a,ih⟩

theorem no_support_where_cast428 {R : SourcePrimitives} {s : I72.State} {qs us ts}
    (same : qs = us) (forest : WhereForest R s qs ts)
    (h : ZeroSupportWhere428 forest) : ZeroSupportWhere428 (same ▸ forest) := by
  cases same
  exact h

theorem selected_leaf_with_zero_outputs_and_no_where_has_no_support428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    (e : Event s q) (safe : ¬ I72.RootCycle s q) (picked : R.elected s q e [])
    (kids : e.kids = []) (empty : q.demand.outputs = []) :
    ZeroSupportSelected428
      (.selected e safe picked .nil (kids.symm ▸ (WhereForest.nil : WhereForest R s [] []))) :=
  ⟨rfl,empty,no_support_where_cast428 kids.symm WhereForest.nil True.intro⟩

theorem original_assembled_trace_has_no_support_or_outputs428
    {R : SourcePrimitives} {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} (root : OriginalPreparedRoot427 f)
    (empty : q.demand.outputs = []) (parentPick : R.elected s q (parentEvent428 root empty) [])
    (localPick : WhereLocal428 R s q f)
    (v : ReviewedForest427 f (List.range f.decl.requirements.length)) :
    ZeroSupportSelected428 (parentTrace428 root empty parentPick localPick v) :=
  ⟨rfl,empty,no_support_where_cast428 (reviewed_source_order_is_entire_original_where427 v)
    (replayWhere428 localPick v) (replayed_original_where_has_no_support_or_outputs428 localPick v)⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere428
