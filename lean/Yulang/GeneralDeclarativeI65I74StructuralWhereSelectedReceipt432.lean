import Yulang.GeneralDeclarativeI65I74StructuralWhereEntry431
import Yulang.GeneralDeclarativeI65SelectedWhereBindings395

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Tree)

/-- Membership of the exact child derivation in the actual named forest,
not membership of only its Event, result key or equal dictionary. -/
inductive ActualForestTraceAt432 (R : SourcePrimitives) (s : I72.State) :
    {qs : List Request} → {ts : List Tree} → WhereForest R s qs ts → Nat →
    {q : Request} → {t : Tree} → {e : Event s q} →
      SourceTrace R s q t (some e) → Prop where
  | here {q : Request} {t qs ts} {e : Event s q}
      (first : SourceTrace R s q t (some e)) (rest : WhereForest R s qs ts) :
      ActualForestTraceAt432 R s (.cons first rest) 0 first
  | there {head q : Request} {ht t qs ts o i} {e : Event s q}
      (first : SourceTrace R s head ht o) {rest : WhereForest R s qs ts}
      {source : SourceTrace R s q t (some e)} :
      ActualForestTraceAt432 R s rest i source →
      ActualForestTraceAt432 R s (.cons first rest) (i+1) source

def ActualWhereTraceAt432 {R : SourcePrimitives} {s : I72.State}
    {q child : Request} {t kt : Tree} {e : Event s child} {parent}
    (trace : SourceTrace R s q t parent) (i : Nat)
    (selected : SourceTrace R s child kt (some e)) : Prop :=
  match trace with
  | .selected _ _ _ _ forest => ActualForestTraceAt432 R s forest i selected
  | .rootK2 _ | .other _ _ _ _ => False

theorem actual_forest_trace_at_keeps_original_request432
    {R : SourcePrimitives} {s : I72.State} {qs ts}
    {forest : WhereForest R s qs ts} {i q t e} {selected : SourceTrace R s q t (some e)}
    (h : ActualForestTraceAt432 R s forest i selected) : qs[i]? = some q := by
  induction h with
  | here => rfl
  | there _ _ ih => simpa using ih

theorem actual_where_trace_at_keeps_original_request432
    {R : SourcePrimitives} {s : I72.State} {q child : Request} {t ct : Tree}
    {a : Event s q} {e : Event s child}
    {trace : SourceTrace R s q t (some a)} {selected : SourceTrace R s child ct (some e)}
    {i : Nat} (h : ActualWhereTraceAt432 trace i selected) : a.kids[i]? = some child := by
  cases trace with
  | selected _ _ _ _ _ => exact actual_forest_trace_at_keeps_original_request432 h

/-- Indexed lookup in the *actual* source forest. A selected summary
forces the original child trace to have a real Event at the requested
ordinal; neither equal dictionary keys nor equal semantic values are
used to find the child. -/
theorem actual_selected_forest_at432 {R : SourcePrimitives} {s : I72.State}
    {qs : List Request} {ts : List Tree} (forest : WhereForest R s qs ts)
    {ds : List Dictionary} (sums : All₂ Summarizes ts (ds.map (.selected)))
    {i : Nat} {child : Request} (whereAt : qs[i]? = some child) :
    ∃ (t : Tree) (d : Dictionary) (e : Event s child)
      (source : SourceTrace R s child t (some e)),
      ActualForestTraceAt432 R s forest i source ∧ ts[i]? = some t ∧ ds[i]? = some d ∧
        Summarizes t (.selected d) := by
  induction i generalizing qs ts ds with
  | zero =>
    cases forest with
    | nil => simp at whereAt
    | @cons x xs t ts oe first rest =>
      cases ds with
      | nil => cases sums
      | cons d ds =>
        cases sums with
        | cons head tail =>
          have now : x = child := by simpa using whereAt
          subst child
          cases head with
          | selected children joined =>
            obtain ⟨e,actual⟩ := named_trace_with_selected_tree_returns_actual_event428 first
            subst t
            exact ⟨_,d,e,first,.here first rest,rfl,rfl,.selected children joined⟩
  | succ i ih =>
    cases forest with
    | nil => simp at whereAt
    | @cons x xs t ts oe first rest =>
      cases ds with
      | nil => cases sums
      | cons d ds =>
        cases sums with
        | cons head tail =>
          obtain ⟨kt,kd,ke,ktree,whereChild,ht,hd,meaning⟩ := ih rest tail (by simpa using whereAt)
          exact ⟨kt,kd,ke,ktree,.there first whereChild,by simpa using ht,by simpa using hd,meaning⟩

/-- The parent's actual selected diagnostic has a concrete source
trace for every original child location it reports as selected. This
is a structural proof on the given trace, not an execution schedule. -/
theorem selected_parent_uses_actual_child_trace432 {R : SourcePrimitives} {s : I72.State}
    {q : Request} {t : Tree} {parent : Event s q} (trace : SourceTrace R s q t (some parent))
    {key : Nat} {ds : List Dictionary} (meaning : Summarizes t (.selected (.node key ds)))
    {i : Nat} {child : Request} (whereAt : parent.kids[i]? = some child) :
    ∃ (kt : Tree) (d : Dictionary) (e : Event s child)
      (childTrace : SourceTrace R s child kt (some e)),
      ActualWhereTraceAt432 trace i childTrace ∧ ds[i]? = some d ∧ Summarizes kt (.selected d) := by
  cases trace with
  | selected event _ _ _ forest =>
    cases meaning with
    | selected children joined =>
      cases joined with
      | selected exact =>
        rw [exact] at children
        obtain ⟨kt,d,e,childTrace,atSource,_,atResult,meaning⟩ :=
          actual_selected_forest_at432 forest children whereAt
        exact ⟨kt,d,e,childTrace,atSource,atResult,meaning⟩


open GeneralDeclarations (OutputBinder Equation)
open GeneralDictionaryAssociatedProvenance (Body)
open CommonDeclaredNominalInspection (Kind)
open CommonNominalFullCarrier (Ty Equivalent)

/-- Join the literal parent output binder to the actual selected child
and the exact typed receipt retained at the requested target. The
same fitting model is used on both sides, but no model is used in
selecting the position, the Event or the typed receipt. This proves
a receipt transfer, not an allocator, a new classifier or a sibling
execution order. -/
theorem actual_where_child_supplies_original_lexical_output432
    {R : SourcePrimitives} (law : SelectedLaw428 R)
    {s : I72.State} {q : Request} {t : Tree} {parent : Event s q}
    (trace : SourceTrace R s q t (some parent))
    {key : Nat} {ds : List Dictionary} (meaning : Summarizes t (.selected (.node key ds)))
    {binder : OutputBinder} {body : Equation}
    (origin : OriginalWhereBinder395 parent.frame binder body) :
    ∃ (kt : Tree) (d : Dictionary) (e : Event s origin.child)
      (source : SourceTrace R s origin.child kt (some e)),
      ActualWhereTraceAt432 trace origin.clauseOrdinal source ∧
      ds[origin.clauseOrdinal]? = some d ∧ Summarizes kt (.selected d) ∧
      (e.outputs origin.outputIndex).receipt.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
      (e.outputs origin.outputIndex).receipt.outputOrdinal = origin.outputOrdinal ∧
      (e.outputs origin.outputIndex).receipt.original = origin.output ∧
      parent.frame.slots (.explicit body) binder.name =
        some ⟨origin.output.target,origin.output.target,origin.output.target⟩ ∧
      ∀ m : I72.Model, I72.Fits s m →
        DictionaryEvidence s m origin.child d ∧
        (∀ k : Kind, sourceRead401 m (parent.frame.slots (.explicit body)) k binder.name () =
          some (m.assignment origin.output.target)) ∧
        ∃ value : Ty, (e.outputs origin.outputIndex).receipt.actualEquation m =
          some (origin.output.target,value) ∧ Equivalent (m.assignment origin.output.target).1 value := by
  have atChild : parent.kids[origin.clauseOrdinal]? = some origin.child :=
    origin.child_position
  obtain ⟨kt,d,e,source,atSource,atResult,childMeaning⟩ :=
    selected_parent_uses_actual_child_trace432 trace meaning atChild
  have exactOutput : origin.child.demand.outputs[origin.outputIndex] = origin.output :=
    (List.getElem?_eq_some_iff.mp origin.outputAt).2
  refine ⟨kt,d,e,source,atSource,atResult,childMeaning,rfl,rfl,exactOutput,origin.slot,?_⟩
  intro m fit
  refine ⟨actual_named_trace_same_model_dictionary428 law source m fit d childMeaning,
    (fun _ => by simp [sourceRead401,origin.slot]),?_⟩
  have target : FixedTargets m e := by
    cases source with
    | selected _ _ chosen _ _ => exact (law chosen m fit).2
  obtain ⟨value,stored,agrees⟩ := target origin.outputIndex
  rw [exactOutput] at stored agrees
  exact ⟨value,stored,agrees⟩

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
