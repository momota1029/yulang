import Yulang.GeneralDeclarativeI65I74LiteralVisitCoordinates473
import Yulang.GeneralDeclarativeI65I74IndependentReadChild484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open CommonRoleCanonicalRows (Row normalize normalize_unique)
open ObservationSyntax471 (Slot ClosedFields literalFields closed_fields_exact sortedFields RecordEntries
  sorted_fields_keep_exact_first_visible_entries)

theorem completely_literal_fields_fix_the_same_independent_closed_source_row
    {s : GeneralDeclarativeHead320.State} {e : Expr} {literal found : Row Expr} {terminal}
    (shape : ClosedFields e literal) (source : Closed s e found terminal) :
    found = literal ∧ terminal = .primitive .emptyRecord [] := by
  induction shape generalizing found terminal with
  | empty =>
    cases source with
    | terminal t => cases t; exact ⟨rfl,rfl⟩
  | field _ ih =>
    cases source with
    | terminal t => cases t
    | field rest =>
      obtain ⟨rfl,rfl⟩ := ih rest
      exact ⟨rfl,rfl⟩

theorem genuinely_selected_old_record_field_is_the_same_ordered_source_child
    {s : GeneralDeclarativeHead320.State} {e : Expr} {literal found selected : Row Expr} {terminal}
    {keys : List Nat} {key : Nat} {child : Expr}
    (shape : literalFields e = some literal) (source : Closed s e found terminal)
    (selectedSource : order (normalize found) keys = some selected)
    (requested : key ∈ keys)
    (actual : (Slot.field key,child) ∈ RecordEntries literal) :
    terminal = .primitive .emptyRecord [] ∧ (key,child) ∈ selected := by
  obtain ⟨aligned,empty⟩ :=
    completely_literal_fields_fix_the_same_independent_closed_source_row (closed_fields_exact.mp shape) source
  rw [aligned] at selectedSource
  refine ⟨empty,?_⟩
  obtain ⟨⟨exactLabel,value⟩,first,eq⟩ := List.mem_map.mp actual
  have keyEq : exactLabel = key := Slot.field.inj (congrArg Prod.fst eq)
  have valEq : value = child := congrArg Prod.snd eq
  subst exactLabel
  subst value
  have was := (sorted_fields_keep_exact_first_visible_entries literal (key,child)).mp first
  exact ((exact_order (normalize_unique literal) selectedSource).2 _).mpr ⟨was,requested⟩



open GeneralDeclarativeInlineTrace331 (TailCode Read Fields)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (lookup_unique)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (lookup lookup_normalize)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

theorem closed_query_spine_is_exactly_the_written_list_when_tail_code_is_a_terminal
    {written all : Row Expr} {tail : Expr}
    (allowed : TailCode tail)
    (showed : literalFields (withTail written tail) = some all) :
    all = written ∧ tail = .primitive .emptyRecord [] := by
  induction written generalizing all with
  | nil =>
    cases allowed <;> simp [withTail,literalFields] at showed ⊢
    exact showed
  | cons x rest ih =>
    rcases x with ⟨key,val⟩
    cases remaining : literalFields (withTail rest tail) with
    | none => simp [withTail,literalFields,remaining] at showed
    | some actual =>
      have eq : (key,val)::actual = all := by simpa [withTail,literalFields,remaining] using showed
      obtain ⟨rfl,endExact⟩ := ih remaining
      exact ⟨eq.symm,endExact⟩

private theorem field_entry_is_in_canonical_row {xs : Row Expr} {k : Nat} {v : Expr}
    (entry : (Slot.field k,v) ∈ RecordEntries xs) : (k,v) ∈ normalize xs := by
  obtain ⟨⟨j,q⟩,picked,eq⟩ := List.mem_map.mp entry
  have jEq : j = k := Slot.field.inj (congrArg Prod.fst eq)
  have qEq : q = v := congrArg Prod.snd eq
  subst j
  subst q
  exact (sorted_fields_keep_exact_first_visible_entries xs (k,v)).mp picked

private theorem field_find_of_lookup {xs : Row Expr} {k : Nat} {v : Expr}
    (read : lookup k xs = some v) : xs.find? (fun x => x.1 == k) = some (k,v) := by
  induction xs with
  | nil => cases read
  | cons x xs ih =>
    rcases x with ⟨j,q⟩
    by_cases hit : k = j
    · subst j
      have qEq : q = v := by simpa [lookup] using read
      subst q
      simp
    · have other : j ≠ k := Ne.symm hit
      simpa [other] using ih (by simpa [lookup,hit] using read)

private theorem exact_field_typing_keeps_the_same_written_labels
    {s : GeneralDeclarativeHead320.State} {m : Mode} {xs ys : Row Expr} {seen}
    (f : Fields s m xs ys seen) : xs.map Prod.fst = ys.map Prod.fst := by
  induction xs generalizing ys seen with
  | nil => cases f; rfl
  | cons _ _ ih => cases f; rename_i tail; simp [ih tail]

theorem fully_literal_record_step_reifies_the_same_independent_child_read
    {s : GeneralDeclarativeHead320.State} {t : Table} {m : Mode} {l k : Nat} {value tail code : Expr}
    {raw printed : Row Expr} {seen} {rawChild childCode : Expr}
    (a : Attached s t)
    (independent : Read (SourceExposure481.authoredView s t) m (.record l value tail) code seen)
    (rawSlice : literalFields (.record l value tail) = some raw)
    (codeSlice : literalFields code = some printed)
    (rawStep : (Slot.field k,rawChild) ∈ RecordEntries raw)
    (codeStep : (Slot.field k,childCode) ∈ RecordEntries printed) :
    ∃ childUses childCard, runReadCard s t m rawChild childCode childCard = some childUses ∧
      Read (SourceExposure481.authoredView s t) m rawChild childCode childUses := by
  cases independent with
  | capture => simp [literalFields] at codeSlice
  | record closed different hasFields orderRead typing tailOk tailRead =>
    obtain ⟨shown,done⟩ := closed_query_spine_is_exactly_the_written_list_when_tail_code_is_a_terminal tailOk codeSlice
    subst printed
    have inCode := field_entry_is_in_canonical_row codeStep
    have codeLookup := lookup_unique (normalize_unique _) inCode
    rw [lookup_normalize] at codeLookup
    have inWritten := GeneralDeclarativeOrderedRecord326.lookup_member codeLookup
    have sameLabels := exact_field_typing_keeps_the_same_written_labels typing
    have keyOrder := (exact_order (normalize_unique _) orderRead).1
    have occurs := List.mem_map_of_mem (f := Prod.fst) inWritten
    rw [←sameLabels,keyOrder] at occurs
    have inRaw := (genuinely_selected_old_record_field_is_the_same_ordered_source_child
      rawSlice closed orderRead occurs rawStep).2
    exact selected_declarative_field_supplies_a_complete_typed_finite_child_card
      a typing k (field_find_of_lookup (lookup_unique (keyOrder.symm ▸ different) inRaw))
      (field_find_of_lookup codeLookup)


open ObservationSyntax471 (Label ReadsDescription)
open LiteralVisits473 (StepWire ReadStep childSlot)

private theorem record_projection_exhibits_exact_literal_fields
    {live : GeneralDeclarativeI65.State} {e : Expr} {label : Label}
    {children : List (Slot × Expr)} {key : Nat} {child : Expr}
    (described : ReadsDescription live e label children)
    (picked : (Slot.field key,child) ∈ children) :
    ∃ (l : Nat) (value tail : Expr) (rows : Row Expr),
      e = .record l value tail ∧ literalFields e = some rows ∧
      (Slot.field key,child) ∈ RecordEntries rows := by
  cases described <;> try simp at picked
  case record spelling =>
    refine ⟨_,_,_,_,rfl,?_,picked⟩
    simp [literalFields,closed_fields_exact.mpr spelling]

theorem original_field_proof_and_actual_old_step_supply_one_independent_typed_child
    {s : GeneralDeclarativeHead320.State} {t : Table} {live : GeneralDeclarativeI65.State}
    {m : Mode} {p : GeneralDeclarationPatterns.Pattern} {w : StepWire}
    {raw code : Expr} {seen} {key : Nat}
    (attach : Attached s t)
    (independent : Read (SourceExposure481.authoredView s t) m raw code seen)
    (edge : ReadStep live w p code raw) (field : w.action = .field key) :
    ∃ childUses childCard,
      runReadCard s t m edge.actualRawChild edge.childQuery childCard = some childUses ∧
      Read (SourceExposure481.authoredView s t) m edge.actualRawChild edge.childQuery childUses := by
  have hit := edge.exactRawChild
  have confirmed := edge.actualQueryChild
  rw [field,childSlot] at hit confirmed
  obtain ⟨_,_,_,_,eq,rawRows,rawEntry⟩ := record_projection_exhibits_exact_literal_fields edge.exactRaw hit
  obtain ⟨_,_,_,_,_,queryRows,queryEntry⟩ := record_projection_exhibits_exact_literal_fields edge.exactQuery confirmed
  subst raw
  exact fully_literal_record_step_reifies_the_same_independent_child_read attach independent rawRows queryRows rawEntry queryEntry

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
