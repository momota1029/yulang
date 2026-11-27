import Yulang.GeneralDeclarativeI65I74OrderedProjectionSafeSet464
import Yulang.GeneralDeclarativeI65I74ProjectionDerivation464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeGraphRows321 (shapeOf observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeEqualities322 (Derives Forest entails)
open GeneralDeclarativeCongruence322 (Congruent Arguments)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Derivation
  (EqWire checkEq exact_finite_data_eq_check_iff_independent_Derives453)

private theorem congruent_with_each_original_alias {s t : State}
    (alias : ∀ a b, Alias s a b → Alias t a b) {a b : Expr}
    (proof : Congruent s a b) : Congruent t a b :=
  Congruent.rec
    (motive_1 := fun a b _ => Congruent t a b)
    (motive_2 := fun a b _ => Arguments t a b)
    (fun h => .variable (alias _ _ h))
    (fun _ ih => .primitive ih)
    (fun _ ih => .nominal ih)
    (fun _ _ p q => .record p q)
    (fun _ ih => .variant ih)
    (fun _ _ p q => .join p q)
    .nil
    (fun _ _ p q => .cons p q)
    proof

/-- Rewrite a syntactic equality proof by replaying its source row leaves
and original alias facts in the target. It does not use model equivalence. -/
theorem original_equational_derives_substitutes_only_its_actual_leaves
    {s t : State} (alias : ∀ a b, Alias s a b → Alias t a b)
    (literals : ∀ r ∈ s.equations, Derives t (.variable r.left) r.right)
    {a b : Expr} (proof : Derives s a b) : Derives t a b :=
  Derives.rec
    (motive_1 := fun a b _ => Derives t a b)
    (motive_2 := fun a b _ => Forest t a b)
    (fun h => literals _ h)
    (fun h => .congruent (congruent_with_each_original_alias alias h))
    (fun x => .refl x)
    (fun _ ih => .symm ih)
    (fun _ _ p q => .trans p q)
    (fun _ ih => .primitive ih)
    (fun _ ih => .nominal ih)
    (fun _ ih => .pairFirst ih)
    (fun _ ih => .pairSecond ih)
    (fun _ _ p q => .record p q)
    (fun _ ih => .variant ih)
    (fun _ _ p q => .join p q)
    .nil
    (fun _ _ p q => .cons p q)
    proof

theorem one_actual_nonalias_derived_row_preserves_all_old_derivation_judgments
    (s : State) (e : Equation) (nonalias : ∀ n, e.right ≠ .variable n)
    (derived : Derives s (.variable e.left) e.right) (a b : Expr) :
    Derives (extendedRows s e) a b ↔ Derives s a b := by
  have same := adding_a_non_alias_row_preserves_actual_aliases s e nonalias
  constructor
  · apply original_equational_derives_substitutes_only_its_actual_leaves
      (fun _ _ p => (same _ _).mp p)
    intro r member
    change r ∈ s.equations ++ [e] at member
    rcases List.mem_append.mp member with old|new
    · exact .row old
    · obtain rfl := List.mem_singleton.mp new
      exact derived
  · apply original_equational_derives_substitutes_only_its_actual_leaves
      (fun _ _ p => (same _ _).mpr p)
    intro r old
    exact .row (List.mem_append_left _ old)

structure DerivedAppendData where
  checked : CheckedAppendData
  derivation : EqWire

def readDerivedAppends (s : State) : List DerivedAppendData → Option State
  | [] => some s
  | e::es =>
    let row := e.checked.row
    if checkEq s (.variable row.left) row.right e.derivation &&
        checksNamedProjectionCut s row.left row.right e.checked.cut then
      readDerivedAppends (extendedRows s row) es
    else none

def AllDeriveInActualPrefix (s : State) : List Equation → Prop
  | [] => True
  | e::es => Derives s (.variable e.left) e.right ∧
      AllDeriveInActualPrefix (extendedRows s e) es

theorem read_derived_batch_validates_exact_supplied_source_proofs_and_cut
    {s t : State} {wire : List DerivedAppendData} (ok : readDerivedAppends s wire = some t) :
    let rows := wire.map fun w => w.checked.row
    OrderedSafeAppends s rows t ∧ AllDeriveInActualPrefix s rows := by
  induction wire generalizing s t with
  | nil =>
    cases Option.some.inj ok
    exact ⟨.done,True.intro⟩
  | cons h tail ih =>
    let r := h.checked.row
    by_cases both : checkEq s (.variable r.left) r.right h.derivation = true ∧
        checksNamedProjectionCut s r.left r.right h.checked.cut = true
    · have yes : readDerivedAppends (extendedRows s r) tail = some t := by
        simpa [readDerivedAppends,r,both.1,both.2] using ok
      obtain ⟨out,derivation⟩ := ih yes
      cases shape : shapeOf r.right with
      | none => simp [checksNamedProjectionCut,shape] at both
      | some form =>
        obtain ⟨safe,returns⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mp
          ⟨h.checked.cut,both.2⟩
        exact ⟨.thenRow shape safe returns out,
          (exact_finite_data_eq_check_iff_independent_Derives453 ..).mp ⟨h.derivation,both.1⟩,derivation⟩
    ·
      simp [readDerivedAppends,Bool.and_eq_true,both,r] at ok

theorem independent_source_and_structural_batch_has_finite_derived_wire
    {s t : State} {rows : List Equation}
    (structural : OrderedSafeAppends s rows t) (native : AllDeriveInActualPrefix s rows) :
    ∃ w, (w.map fun z => z.checked.row) = rows ∧ readDerivedAppends s w = some t := by
  induction structural with
  | done => exact ⟨[],rfl,rfl⟩
  | @thenRow form s e es t shape safe noReturn _ ih =>
    obtain ⟨first,rest⟩ := native
    obtain ⟨eq,p⟩ := (exact_finite_data_eq_check_iff_independent_Derives453 ..).mpr first
    obtain ⟨cut,c⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mpr ⟨safe,noReturn⟩
    obtain ⟨ws,rows,passed⟩ := ih rest
    exact ⟨⟨⟨e,cut⟩,eq⟩::ws,by simp [rows],by simp [readDerivedAppends,p,c,passed]⟩

theorem all_certified_equations_are_derivable_from_original_unextended_rows_and_vice_versa
    {s t : State} {rows : List Equation}
    (structural : OrderedSafeAppends s rows t) (derived : AllDeriveInActualPrefix s rows)
    (a b : Expr) : Derives t a b ↔ Derives s a b := by
  induction structural with
  | done => rfl
  | @thenRow form s e es t shape _ _ _ ih =>
    obtain ⟨first,rest⟩ := derived
    have nonAlias : ∀ n, e.right ≠ .variable n := by
      intro n eq
      rw [eq] at shape
      cases shape
    exact (ih rest).trans (one_actual_nonalias_derived_row_preserves_all_old_derivation_judgments s e nonAlias first a b)

private theorem actual_derives_supply_separate_entailment (s : State) (rows : List Equation)
    (has : AllDeriveInActualPrefix s rows) :
    AllEntailedInItsActualPrefix s rows := by
  induction rows generalizing s with
  | nil => exact True.intro
  | cons e es ih => exact ⟨entails has.1,ih _ has.2⟩

theorem checked_derived_batch_preserves_all_exact_ordinary_models_and_raw_cycles
    {s t : State} {wire : List DerivedAppendData} (ok : readDerivedAppends s wire = some t)
    (m : Assignment) (a : Nat) :
    (Models t m ↔ Models s m) ∧
    (AliasCycle t (observed t) a ↔ AliasCycle s (observed s) a) := by
  obtain ⟨typed,derived⟩ := read_derived_batch_validates_exact_supplied_source_proofs_and_cut ok
  exact ⟨batch_keeps_all_original_ordinary_models_under_separate_entailment typed
      (actual_derives_supply_separate_entailment _ _ derived) m,
    accepted_batch_preserves_every_exact_original_k2 typed a⟩


theorem exact_finite_derived_batch_iff_independent_actual_prefix_judgments
    {s t : State} {rows : List Equation} :
    (∃ w, (w.map fun z => z.checked.row) = rows ∧ readDerivedAppends s w = some t) ↔
      OrderedSafeAppends s rows t ∧ AllDeriveInActualPrefix s rows := by
  constructor
  · rintro ⟨w,rfl,yes⟩
    exact read_derived_batch_validates_exact_supplied_source_proofs_and_cut yes
  · rintro ⟨h,p⟩
    exact independent_source_and_structural_batch_has_finite_derived_wire h p

theorem independent_prefix_derivations_are_iff_literal_derivability_in_first_state
    {s t : State} {rows : List Equation} (h : OrderedSafeAppends s rows t) :
    AllDeriveInActualPrefix s rows ↔
      ∀ e ∈ rows, Derives s (.variable e.left) e.right := by
  induction h with
  | done => simp [AllDeriveInActualPrefix]
  | @thenRow form s r rows t shape _ _ _ ih =>
    have noAlias : ∀ n, r.right ≠ .variable n := by
      intro n eq
      rw [eq] at shape
      cases shape
    constructor
    · rintro ⟨head,tail⟩ e got
      rcases List.mem_cons.mp got with eq|later
      · exact eq.symm ▸ head
      · exact (one_actual_nonalias_derived_row_preserves_all_old_derivation_judgments s r noAlias
          head _ _).mp (ih.mp tail e later)
    · intro all
      have head := all r List.mem_cons_self
      refine ⟨head,ih.mpr ?_⟩
      intro e later
      exact (one_actual_nonalias_derived_row_preserves_all_old_derivation_judgments s r noAlias
        head _ _).mpr (all e (List.mem_cons_of_mem _ later))

theorem complete_derived_batch_uses_initial_actual_derivability_and_final_safe_touched_roots
    (s : State) (rows : List Equation) :
    (∃ w, (w.map fun z => z.checked.row) = rows ∧
      readDerivedAppends s w = some (GeneralDeclarativeEntailment320.appendFacts s rows)) ↔
    ((∀ e ∈ rows, ∃ h, shapeOf e.right = some h) ∧
      (∀ e ∈ rows, ¬AliasCycle (GeneralDeclarativeEntailment320.appendFacts s rows)
        (observed (GeneralDeclarativeEntailment320.appendFacts s rows)) e.left)) ∧
    (∀ e ∈ rows, Derives s (.variable e.left) e.right) := by
  rw [exact_finite_derived_batch_iff_independent_actual_prefix_judgments]
  constructor
  · rintro ⟨guard,source⟩
    exact ⟨(whole_named_batch_safety_iff_every_touched_final_root_is_safe ..).mp guard,
      (independent_prefix_derivations_are_iff_literal_derivability_in_first_state guard).mp source⟩
  · rintro ⟨safe,original⟩
    have guard := (whole_named_batch_safety_iff_every_touched_final_root_is_safe ..).mpr safe
    exact ⟨guard,(independent_prefix_derivations_are_iff_literal_derivability_in_first_state guard).mpr original⟩

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
