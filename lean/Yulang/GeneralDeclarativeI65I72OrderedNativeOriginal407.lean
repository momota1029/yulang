import Yulang.GeneralDeclarativeI65I72OrderedNativeClassifies407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

structure ExactOrderedNativeInput407 {s q need} (input : NativeElectionInput407 s q need) where
  typedOrdinal : Nat
  actual : NativeActualPath407 input
  exactRow : s.core.origins[typedOrdinal]? = some actual.original

def ExactOrderedNativeInput407.address {s q need input}
    (read : ExactOrderedNativeInput407 (s := s) (q := q) (need := need) input) : NativeInputAddress406 :=
  ⟨q.occurrence,0,[0],read.typedOrdinal⟩

theorem original_ordered_payload_from_exact_input407 {s q need}
    (input : NativeElectionInput407 s q need) (n : Nat) (original : Origin)
    (atN : s.core.origins[n]? = some original) (route : OriginRoute s.core original input.read.arg.center)
    {name : Nat} (decoded : literalUnaryPayloadName406 input.read.found original.endpoint = some name)
    (bounds : Bounds s.core.current.ordinary ⟨input.read.sourcePayload,name,input.positive.upperPayload⟩) :
    ∃ read : ExactOrderedNativeInput407 input,
      read.address = ⟨q.occurrence,0,[0],n⟩ ∧ read.actual.original = original ∧ read.actual.name = name := by
  let actual : NativeActualPath407 input := ⟨original,List.mem_of_getElem? atN,route,name,decoded,bounds⟩
  exact ⟨⟨n,actual,atN⟩,rfl,rfl,rfl⟩

theorem same_actual_typed_address_preserves_ordered_body_capture407 {s q need}
    {input : NativeElectionInput407 s q need} (e : ElectedNativeHead407 input)
    (a b : ExactOrderedNativeInput407 input) (same : a.address = b.address) :
    a.actual.original = b.actual.original ∧ a.actual.name = b.actual.name ∧
    (OrderedNativeFrame407 e a.actual).input = (OrderedNativeFrame407 e b.actual).input := by
  have index := congrArg NativeInputAddress406.originalSourceOrdinal same
  change a.typedOrdinal = b.typedOrdinal at index
  have exactSource := a.exactRow
  rw [index,b.exactRow] at exactSource
  have orig := Option.some.inj exactSource.symm
  have term := a.actual.decoded
  rw [orig,b.actual.decoded] at term
  have name := Option.some.inj term.symm
  refine ⟨orig,name,?_⟩
  unfold OrderedNativeFrame407 frameAtSource395
  rw [name]

theorem exact_ordered_native_has_original_B6_body407 {s q need}
    {input : NativeElectionInput407 s q need} (e : ElectedNativeHead407 input)
    (actual : NativeActualPath407 input)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : NamedInputAtStoredHead401 s.b6 (OrderedNativeFrame407 e actual)) :
    Nonempty (∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 (OrderedNativeFrame407 e actual) i) := by
  classical
  let f := OrderedNativeFrame407 e actual
  have check := input.checked.2 f.decl (List.mem_of_getElem? f.authored)
  have role := (visible_exact s.core q f.decl).mp f.inScope |>.2
  have arity : q.demand.arguments.length = f.decl.head.length := by
    change q.demand.arguments.length = (visible s.core q)[e.winner].head.length
    rw [input.read.argAt,e.source.unary.literal]
    rfl
  have output (i : Fin q.demand.outputs.length) : Nonempty (NamedMixedOutput401 s.b6 f i) := by
    obtain ⟨body,supply⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
      (authoredRegistry s.core.current).roles f.decl check.signature q.demand.outputs[i].name (role ▸ declared i)
    obtain ⟨plan,original⟩ := typed i body supply
    obtain ⟨rhs,substituted⟩ := exact_mixed_names_are_substitutable401 (f.slots body) plan
      (original_frame_slot_coverage399 f input.checked arity
        (default_positions_from_authored_role_decl399 s.core) supply)
    exact ⟨⟨body,supply,plan,original,rhs,substituted⟩⟩
  exact ⟨fun i => Classical.choice (output i)⟩

theorem exact_ordered_native_retains_written_ordinal_and_target407 {s q need}
    {input : NativeElectionInput407 s q need} {trees}
    (step : OrderedNativeStep407 input trees) :
    step.written.length = q.demand.outputs.length ∧
    ∀ i : Fin q.demand.outputs.length,
      step.written[i.val]? = some (step.output i).receipt ∧
      (step.output i).receipt.occurrence = q.occurrence ∧
      (step.output i).receipt.outputOrdinal = i.val ∧
      (step.output i).receipt.original = q.demand.outputs[i] := by
  refine ⟨by simp [OrderedNativeStep407.written],fun i => ?_⟩
  rw [OrderedNativeStep407.written,List.getElem?_ofFn,dite_eq_left i.isLt]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem same_ordered_native_frame_generates_original_where407 {s q need}
    {input : NativeElectionInput407 s q need} {trees}
    (step : OrderedNativeStep407 input trees) {j : Nat} {clause : Clause}
    (written : step.elected.row.requirements[j]? = some clause) :
    ∃ binders : List Nat, clause.arguments = binders.map Pattern.var ∧
      (frameWhereKids400 step.frame)[j]? = some (⟨q.occurrence ++ [j],⟨clause.role,
        binders.map step.frame.input,[]⟩⟩ : Request) :=
  literal_where_child_at403 step.frame step.clauses input.checked written

end Yulang.GeneralDeclarativeI65.I72
