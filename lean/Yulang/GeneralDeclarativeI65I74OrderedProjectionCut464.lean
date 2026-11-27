import Yulang.GeneralDeclarativeI65I74ProjectionCutExact464
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeEntailment320 (Entails Holds model_append conservative_append)
open GeneralNominalCommonBridge (Assignment)
open Yulang.GeneralDeclarativeI65.I72.List410 (ExactEscapeWire)

structure CheckedAppendData where
  row : Equation
  cut : ExactEscapeWire

/-- Reads only finite supplied rows and cuts. This is an abstract replay in a
separate ordinary snapshot, not a graph mutation, origin issuer or allocator. -/
def readOrderedAppends (s : State) : List CheckedAppendData → Option State
  | [] => some s
  | e :: es =>
    if checksNamedProjectionCut s e.row.left e.row.right e.cut then
      readOrderedAppends (extendedRows s e.row) es
    else none

/-- Independent mathematical guard in each actual prefix. No negative graph
proof or model assignment appears in the wire datatype. -/
inductive OrderedSafeAppends : State → List Equation → State → Prop where
  | done : OrderedSafeAppends s [] s
  | thenRow : shapeOf e.right = some form →
      ¬ AliasCycle s (observed s) e.left →
      (∀ child ∈ form.children, ∀ a, Alias s a e.left → ¬ Path (structural s) child a) →
      OrderedSafeAppends (extendedRows s e) es t →
      OrderedSafeAppends s (e::es) t

theorem every_checked_append_result_reads_exact_order
    {s t : State} {wire : List CheckedAppendData} (ok : readOrderedAppends s wire = some t) :
    OrderedSafeAppends s (wire.map CheckedAppendData.row) t := by
  induction wire generalizing s t with
  | nil =>
    cases Option.some.inj ok
    exact .done
  | cons e es ih =>
    by_cases accepts : checksNamedProjectionCut s e.row.left e.row.right e.cut = true
    · have tail : readOrderedAppends (extendedRows s e.row) es = some t := by
        simpa [readOrderedAppends,accepts] using ok
      cases form : shapeOf e.row.right with
      | none => simp [checksNamedProjectionCut,form] at accepts
      | some h =>
        obtain ⟨safe,returnproof⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe form).mp
          ⟨e.cut,accepts⟩
        exact .thenRow form safe returnproof (ih tail)
    · simp [readOrderedAppends,accepts] at ok

theorem each_independent_ordered_safe_append_has_exact_finite_batch
    {s : State} {rows : List Equation} {t : State} (h : OrderedSafeAppends s rows t) :
    ∃ wire : List CheckedAppendData, wire.map CheckedAppendData.row = rows ∧
      readOrderedAppends s wire = some t := by
  induction h with
  | done => exact ⟨[],rfl,rfl⟩
  | @thenRow form s e es t shape safe nonreturns _ ih =>
    obtain ⟨key,yes⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mpr
      ⟨safe,nonreturns⟩
    obtain ⟨keys,same,rest⟩ := ih
    exact ⟨⟨e,key⟩ :: keys,by simp [same],by simp [readOrderedAppends,yes,rest]⟩

theorem ordered_append_exact_independent_guard {s : State} {rows : List Equation} {t : State} :
    OrderedSafeAppends s rows t ↔
      ∃ wire : List CheckedAppendData, wire.map CheckedAppendData.row = rows ∧
        readOrderedAppends s wire = some t := by
  constructor
  · exact each_independent_ordered_safe_append_has_exact_finite_batch
  · rintro ⟨wire,rfl,ok⟩
    exact every_checked_append_result_reads_exact_order ok

theorem literal_row_order_and_ordinary_constraints_are_exact
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t) :
    t.normal = s.normal ∧ t.equations = s.equations ++ rows := by
  induction h with
  | done => simp
  | thenRow _ _ _ _ ih =>
    obtain ⟨n,w⟩ := ih
    exact ⟨n,by simpa [extendedRows,List.append_assoc] using w⟩

theorem accepted_old_row_ordinal_is_unchanged
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t)
    {i : Nat} {r : Equation} (found : s.equations[i]? = some r) :
    t.equations[i]? = some r := by
  rw [(literal_row_order_and_ordinary_constraints_are_exact h).2]
  have lt : i<s.equations.length := List.getElem?_eq_some_iff.mp found |>.choose
  simpa [List.getElem?_append_left lt] using found

theorem accepted_new_row_has_exact_appended_ordinal
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t)
    {i : Nat} {r : Equation} (found : rows[i]? = some r) :
    t.equations[s.equations.length+i]? = some r := by
  rw [(literal_row_order_and_ordinary_constraints_are_exact h).2,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simpa only [Nat.add_sub_cancel_left] using found

theorem accepted_batch_preserves_exact_original_aliases
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t) (a b : Nat) :
    Alias t a b ↔ Alias s a b := by
  induction h with
  | done => rfl
  | @thenRow form s e es t shape _ _ _ ih =>
    have nonalias : ∀ n, e.right ≠ .variable n := by
      intro n caseVar
      rw [caseVar] at shape
      cases shape
    exact ih.trans (adding_a_non_alias_row_preserves_actual_aliases s e nonalias a b)

theorem accepted_batch_preserves_every_exact_original_k2
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t) (a : Nat) :
    AliasCycle t (observed t) a ↔ AliasCycle s (observed s) a := by
  induction h with
  | done => rfl
  | @thenRow form s e es t shape _ nonreturns _ ih =>
    have nonalias : ∀ n, e.right ≠ .variable n := by
      intro n caseVar
      rw [caseVar] at shape
      cases shape
    apply ih.trans
    rcases e with ⟨root,ex⟩
    exact one_nonalias_raw_row_does_not_change_k2_under_original_class_no_return s root ex nonalias
      (by
        intro q h child member near alias
        have eq : q = form := Option.some.inj (h.symm.trans shape)
        subst q
        exact nonreturns child member near alias) a

/-- A second, independently supplied fact about the staged mathematical models.
Soundness of a graph cut alone does not imply this fact: it supplies no
equation entailment and no native source information. -/
def AllEntailedInItsActualPrefix (s : State) : List Equation → Prop
  | [] => True
  | e :: es => Entails s e ∧ AllEntailedInItsActualPrefix (extendedRows s e) es

theorem batch_keeps_all_original_ordinary_models_under_separate_entailment
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t)
    (licensed : AllEntailedInItsActualPrefix s rows) (m : Assignment) :
    Models t m ↔ Models s m := by
  induction h with
  | done => rfl
  | @thenRow form s e es t _ _ _ _ ih =>
    obtain ⟨atPrefix,later⟩ := licensed
    have same : Models (extendedRows s e) m ↔ Models s m :=
      conservative_append (rows := [e]) (fun r seen => (List.mem_singleton.mp seen).symm ▸ atPrefix) m
    exact (ih later).trans same

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
