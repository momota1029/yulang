import Yulang.GeneralDeclarativeI65B6TapePreoutput399
import Yulang.GeneralDeclarativeI65SameEventSemantics388

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Equation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)

/-- Lookup over every original output position, with `none` left in
place. In particular missing B6 data never shift later outputs. -/
def logicalEventOutputs399 {s q} (event : LiteralLocalEvent s q)
    (atlas : B6SymbolicAtlas398 s)
    (unique : (event.declaration.associated.map Equation.name).Nodup) :
    List (Option CompoundEquation394) :=
  List.ofFn fun i => (logicalOutputOfEvent399 event atlas i unique).map EventLogicalOutput399.equation

theorem logical_event_list_exact_ordinal399 {s q} (event : LiteralLocalEvent s q)
    (atlas : B6SymbolicAtlas398 s) (unique : (event.declaration.associated.map Equation.name).Nodup)
    (i : Fin q.demand.outputs.length) :
    (logicalEventOutputs399 event atlas unique).length = q.demand.outputs.length ∧
      (logicalEventOutputs399 event atlas unique)[i.val]? =
        some ((logicalOutputOfEvent399 event atlas i unique).map EventLogicalOutput399.equation) := by
  simp [logicalEventOutputs399,i.isLt]

/-- C386's existing original-supply premise identifies the supplier
already associated with the same ordinal. This picks neither literal
output syntax nor a model-dependent value. -/
theorem literal_event_original_supplier399 {s q}
    (event : LiteralLocalEvent s q) (i : Fin q.demand.outputs.length) :
    ∃ rec, event.receipts[i.val]? = some rec ∧ rec.requested = q.demand.outputs[i] ∧
      Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name rec.source := by
  have whereIndex : i.val < event.receipts.length := by rw [event.receiptCount]; exact i.isLt
  have got := List.getElem?_eq_getElem whereIndex
  obtain ⟨_,_,asked,supplier,_⟩ := event.receiptAt i.val _ got
  have same := (List.getElem?_eq_some_iff.mp asked).2
  exact ⟨_,got,same.symm,same ▸ supplier⟩

/-- Only the original requested output and its supplier are aligned
against the literal ledger. The logical code is established from B6
plus the same exact event slots, not taken from `rec.written`. -/
def B6EventRhsMeaning399 {s : State} (atlas : B6SymbolicAtlas398 s) (e : LiteralEvent s) : Prop :=
  ∀ i : Fin e.1.demand.outputs.length,
    ∃ (unique : (e.2.declaration.associated.map Equation.name).Nodup)
      (out : EventLogicalOutput399 e.2 i) (rec : OrderedReceipt),
      (logicalEventOutputs399 e.2 atlas unique)[i.val]? = some (some out.equation) ∧
      e.2.receipts[i.val]? = some rec ∧
      out.body = rec.source ∧ out.equation.requested = rec.requested ∧
      out.equation.occurrence = rec.occurrence ∧ out.equation.ordinal = rec.ordinal ∧
      CompoundSourceRhs394 s (writtenBodySlot392 e.2 out.body) false
        (normalize (bodyPattern out.body)) out.equation.rhs

/-- B6 is called only for a selected local source event established
by the independent rule at its original source. This condition does
not supply the event, choose the impl, or assert semantic soundness. -/
def SuppliesSymbolicB6AtEvents399 [judgment : ReplayJudgment] (s : State)
    (atlas : B6SymbolicAtlas398 s) : Prop :=
  ∀ (q : Request) (event : LiteralLocalEvent s q),
    LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩ →
    ∀ (i : Fin q.demand.outputs.length) (source : Body),
      Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name source →
      ∃ p : B6ValuePlan398 s false (normalize (bodyPattern source)),
        atlas.read event.declarationOrdinal source = some p ∧
        B6UsesFit398 s (writtenBodySlot392 event source) p.needs

theorem B6_local_logical_rhs_on_exact_event399 [judgment : ReplayJudgment]
    {s q} (event : LiteralLocalEvent s q)
    (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6SymbolicAtlas398 s) (b6 : SuppliesSymbolicB6AtEvents399 (judgment := judgment) s atlas) :
    B6EventRhsMeaning399 atlas ⟨q,event⟩ := by
  intro i
  obtain ⟨rec,retained,requested,supplied⟩ := literal_event_original_supplier399 event i
  obtain ⟨p,annotation,fit⟩ := b6 q event guard i rec.source supplied
  have unique := (checked.2 event.declaration (List.mem_of_getElem? event.declaredAt)).identified.2.2.1
  obtain ⟨out,written,source,meaning⟩ :=
    event_B6_source_produces_logical_rhs399 event atlas i unique supplied annotation fit
  obtain ⟨occurrence,ordinal,_,_,_⟩ := event.receiptAt i.val rec retained
  refine ⟨unique,out,rec,?_,retained,source,requested.symm,occurrence.symm,ordinal.symm,?_⟩
  · rw [(logical_event_list_exact_ordinal399 event atlas unique i).2,written]
    rfl
  · rw [source]
    exact meaning

/-- All exact original occurrences in this finite selected dictionary
are covered by the logical source relation when B6 supplies the
indexed source plan and slot compatibility. This is not a mixed
literal-wire theorem and not an all-state classifier producer. -/
theorem addressed_ledger_B6_logical_rhs399 [judgment : ReplayJudgment]
    {s q d events} (addressed : AddressedDictionaryEvents (judgment := judgment) s q d events)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6SymbolicAtlas398 s) (b6 : SuppliesSymbolicB6AtEvents399 (judgment := judgment) s atlas) :
    LedgerMeaning (B6EventRhsMeaning399 atlas) events := by
  exact AddressedDictionaryEvents.rec
    (motive_1 := fun _ _ e _ => LedgerMeaning (B6EventRhsMeaning399 atlas) e)
    (motive_2 := fun _ _ e _ => LedgerForestMeaning (B6EventRhsMeaning399 atlas) e)
    (fun event guard _ kids => ⟨B6_local_logical_rhs_on_exact_event399 event guard checked atlas b6,kids⟩)
    True.intro
    (fun _ _ first rest => ⟨first,rest⟩)
    addressed

end Yulang.GeneralDeclarativeI65
