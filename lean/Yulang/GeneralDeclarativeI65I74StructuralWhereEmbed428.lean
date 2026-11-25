import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedPosition428

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open CommonRoleOutermostResolver (Tree Summarizes)
open I72 (Event SourcePrimitives SourceTrace WhereForest SupportForest)
open I72.Check408 (Write)

/-- Pure rule inclusion. The State, exact original Event, child request
and original producer receipt are unchanged by the map. -/
structure NamedRuleMap428 (A B : SourcePrimitives) : Prop where
  elected : ∀ {s q e needs}, A.elected s q e needs → B.elected s q e needs
  other : ∀ {s q v needs}, A.other s q v needs → B.other s q v needs

theorem left_named_rule_map428 (A B : SourcePrimitives) : NamedRuleMap428 A (ruleUnion428 A B) :=
  ⟨fun h => .inl h,fun h => .inl h⟩

theorem right_named_rule_map428 (A B : SourcePrimitives) : NamedRuleMap428 B (ruleUnion428 A B) :=
  ⟨fun h => .inr h,fun h => .inr h⟩

noncomputable def namedTraceWrites428 {R : SourcePrimitives} {s q t o}
    (trace : SourceTrace R s q t o) : List Write :=
  SourceTrace.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun e _ _ _ _ _ kids => I72.Check408.encodedEventWrites e ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) trace

noncomputable def namedForestWrites428 {R : SourcePrimitives} {s qs ts}
    (forest : WhereForest R s qs ts) : List Write :=
  WhereForest.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun e _ _ _ _ _ kids => I72.Check408.encodedEventWrites e ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) forest

theorem named_writes_are_the_current_R13_writes428 {s q t o}
    (trace : SourceTrace I72.RepeatedCenters421.R13 s q t o) :
    namedTraceWrites428 trace = I72.RepeatedCenters421.writes trace := rfl

/-- The complete support journal (including recursively used prior
producers); the entries retain their exact occurrence, dictionary,
output ordinal and receipt, not merely their cardinality. -/
noncomputable def namedTraceNeeds428 {R : SourcePrimitives} {s q t o}
    (trace : SourceTrace R s q t o) : List (I72.OutputNeed s) :=
  SourceTrace.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ _ => List (I72.OutputNeed s))
    (motive_2 := fun _ _ _ => List (I72.OutputNeed s))
    (motive_3 := fun _ _ => List (I72.OutputNeed s))
    (fun _ => []) (fun _ _ _ _ support => support)
    (fun _ _ _ _ _ support kids => support ++ kids)
    [] (fun _ _ a b => a ++ b)
    [] (fun {_ _ n _} _ _ _ _ a b => n :: (a ++ b))
    trace

noncomputable def namedWhereNeeds428 {R : SourcePrimitives} {s qs ts}
    (forest : WhereForest R s qs ts) : List (I72.OutputNeed s) :=
  WhereForest.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ _ => List (I72.OutputNeed s))
    (motive_2 := fun _ _ _ => List (I72.OutputNeed s))
    (motive_3 := fun _ _ => List (I72.OutputNeed s))
    (fun _ => []) (fun _ _ _ _ support => support)
    (fun _ _ _ _ _ support kids => support ++ kids)
    [] (fun _ _ a b => a ++ b)
    [] (fun {_ _ n _} _ _ _ _ a b => n :: (a ++ b))
    forest

noncomputable def namedSupportNeeds428 {R : SourcePrimitives} {s asks}
    (need : SupportForest R s asks) : List (I72.OutputNeed s) :=
  SupportForest.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ _ => List (I72.OutputNeed s))
    (motive_2 := fun _ _ _ => List (I72.OutputNeed s))
    (motive_3 := fun _ _ => List (I72.OutputNeed s))
    (fun _ => []) (fun _ _ _ _ support => support)
    (fun _ _ _ _ _ support kids => support ++ kids)
    [] (fun _ _ a b => a ++ b)
    [] (fun {_ _ n _} _ _ _ _ a b => n :: (a ++ b))
    need

/-- Transport of the actual checked derivation. The same selected
Event, source-order where traces, all needs and their actual proofs
remain. It never calls a second checker, reallocates a capture, or
executes/charges a prior support producer a second time. -/
noncomputable def mapNamedTrace428 {A B : SourcePrimitives} (rule : NamedRuleMap428 A B)
    {s q t o} (trace : SourceTrace A s q t o) :
    {replay : SourceTrace B s q t o //
      namedTraceWrites428 replay = namedTraceWrites428 trace ∧
      namedTraceNeeds428 replay = namedTraceNeeds428 trace} := by
  exact SourceTrace.rec (R := A) (s := s)
    (motive_1 := fun q t o a => {b : SourceTrace B s q t o //
      namedTraceWrites428 b = namedTraceWrites428 a ∧ namedTraceNeeds428 b = namedTraceNeeds428 a})
    (motive_2 := fun qs ts a => {b : WhereForest B s qs ts //
      namedForestWrites428 b = namedForestWrites428 a ∧ namedWhereNeeds428 b = namedWhereNeeds428 a})
    (motive_3 := fun needs a => {b : SupportForest B s needs //
      namedSupportNeeds428 b = namedSupportNeeds428 a})
    (fun cycle => ⟨.rootK2 cycle,rfl,rfl⟩)
    (fun verdict safe picked _ support =>
      ⟨.other verdict safe (rule.other picked) support.val,rfl,support.property⟩)
    (fun e safe picked supports original support children => by
      refine ⟨.selected e safe (rule.elected picked) support.val children.val,?_,?_⟩
      · change I72.Check408.encodedEventWrites e ++ namedForestWrites428 children.val =
          I72.Check408.encodedEventWrites e ++ namedForestWrites428 original
        rw [children.property.1]
      · change namedSupportNeeds428 support.val ++ namedWhereNeeds428 children.val =
          namedSupportNeeds428 supports ++ namedWhereNeeds428 original
        rw [support.property,children.property.2])
    ⟨.nil,rfl,rfl⟩
    (fun oldA oldB a b => by
      refine ⟨.cons a.val b.val,?_,?_⟩
      · change namedTraceWrites428 a.val ++ namedForestWrites428 b.val =
          namedTraceWrites428 oldA ++ namedForestWrites428 oldB
        rw [a.property.1,b.property.1]
      · change namedTraceNeeds428 a.val ++ namedWhereNeeds428 b.val =
          namedTraceNeeds428 oldA ++ namedWhereNeeds428 oldB
        rw [a.property.2,b.property.2])
    ⟨.nil,rfl⟩
    (fun {_ _ n _} oldA finished receipt oldB support rest => by
      refine ⟨.cons support.val finished receipt rest.val,?_⟩
      change n :: (namedTraceNeeds428 support.val ++ namedSupportNeeds428 rest.val) =
        n :: (namedTraceNeeds428 oldA ++ namedSupportNeeds428 oldB)
      rw [support.property.2,rest.property])
    trace

private theorem selected_shape_exports_event428 {R : SourcePrimitives}
    {s q t key kids option} (trace : SourceTrace R s q t option)
    (shape : t = .selected key kids) : ∃ event : Event s q, option = some event := by
  cases trace with
  | rootK2 => cases shape
  | other verdict _ _ _ => cases verdict <;> cases shape
  | selected => exact ⟨_,rfl⟩

theorem named_trace_with_selected_tree_returns_actual_event428 {R : SourcePrimitives}
    {s q key kids option} (t : SourceTrace R s q (.selected key kids) option) :
    ∃ event : Event s q, option = some event :=
  selected_shape_exports_event428 t rfl

theorem actual_parent_second_selected_is_the_supplied_existing_event428
    {R : SourcePrimitives} {s : I72.State} {q : Request} (e : Event s q)
    (a : OriginalRecordArgument427 e.frame 0 0) (b : LiteralVariableArgumentAt428 e.frame 1)
    (two : e.frame.decl.requirements.length = 2) (safe : ¬ I72.RootCycle s q)
    (picked : R.elected s q e [])
    {ta tb oa} {existing : Event s b.child}
    (first : SourceTrace R s a.child ta oa)
    (second : SourceTrace R s b.child tb (some existing)) :
    TraceChild428 (assembleActualMixedSiblings428 e a b two safe picked first second)
      1 b.child existing := by
  let written : WhereForest R s [a.child,b.child] [ta,tb] := .cons first (.cons second .nil)
  have here : SelectedAt428 R s written 1 b.child existing :=
    .there first (.here second .nil)
  have transport : ∀ qs (same : [a.child,b.child] = qs),
      SelectedAt428 R s (same ▸ written) 1 b.child existing := by
    intro qs same
    cases same
    exact here
  exact transport e.kids (literal_mixed_where_order_has_original_distinct_children428 a b two).symm

theorem selected_trace_local_witness_has_empty_needs428
    {R : SourcePrimitives} {s q t} {e : Event s q} (trace : SourceTrace R s q t (some e))
    (zero : ZeroSupportSelected428 trace) : R.elected s q e [] := by
  cases trace with
  | selected _ _ picked _ _ =>
    exact zero.1 ▸ picked

theorem event_with_no_original_outputs_encodes_no_writes428
    {s q} (e : Event s q) (none : q.demand.outputs = []) :
    I72.Check408.encodedEventWrites e = [] :=
  List.length_eq_zero_iff.mp (by simp [I72.Check408.encodedEventWrites,none])

theorem support_free_original_named_trace_encodes_no_writes428
    {R : SourcePrimitives} {s q t option} (trace : SourceTrace R s q t option)
    (zero : ZeroSupportSelected428 trace) : namedTraceWrites428 trace = [] := by
  exact SourceTrace.rec (R:=R) (s:=s)
    (motive_1 := fun _ _ _ a => ZeroSupportSelected428 a → namedTraceWrites428 a = [])
    (motive_2 := fun _ _ a => ZeroSupportWhere428 a → namedForestWrites428 a = [])
    (motive_3 := fun _ _ => True)
    (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun event _ _ _ kids _ recursive zero => by
      change I72.Check408.encodedEventWrites event ++ namedForestWrites428 kids = []
      rw [event_with_no_original_outputs_encodes_no_writes428 event zero.2.1,recursive zero.2.2]
      rfl)
    (fun _ => rfl)
    (fun left right hleft hright zero => by
      change namedTraceWrites428 left ++ namedForestWrites428 right = []
      rw [hleft zero.1,hright zero.2]
      rfl)
    True.intro (fun _ _ _ _ _ _ => True.intro)
    trace zero

theorem assembled_mixed_named_trace_exact_writes428
    {R : SourcePrimitives} {s : I72.State} {q : Request} (e : Event s q)
    (a : OriginalRecordArgument427 e.frame 0 0) (b : LiteralVariableArgumentAt428 e.frame 1)
    (two : e.frame.decl.requirements.length = 2) (safe : ¬ I72.RootCycle s q)
    (picked : R.elected s q e [])
    {ta tb oa ob} (first : SourceTrace R s a.child ta oa) (second : SourceTrace R s b.child tb ob) :
    namedTraceWrites428 (assembleActualMixedSiblings428 e a b two safe picked first second) =
      I72.Check408.encodedEventWrites e ++ (namedTraceWrites428 first ++ namedTraceWrites428 second) := by
  let forest : WhereForest R s [a.child,b.child] [ta,tb] := .cons first (.cons second .nil)
  have alignment : ∀ qs (eq : [a.child,b.child] = qs),
      namedForestWrites428 (eq ▸ forest) = namedTraceWrites428 first ++ namedTraceWrites428 second := by
    intro qs eq
    cases eq
    change namedTraceWrites428 first ++ (namedTraceWrites428 second ++ []) = _
    rw [List.append_nil]
  change I72.Check408.encodedEventWrites e ++ namedForestWrites428
      ((literal_mixed_where_order_has_original_distinct_children428 a b two).symm ▸ forest) = _
  rw [alignment]

end Yulang.GeneralDeclarativeI65.StructuralWhere428
