import Yulang.GeneralDeclarativeI65I74StructuralWherePairRead427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Visit fieldPatterns PatternK2 variable_has_no_visit)
open I72.List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410
  exact_escape_preserves_alias_side410)

/-- Only the label the actual patterns inspect is restricted. Other
fields, classes and unsupported raw rows remain part of the raw graph. -/
private def oneQueriedField427 (w : ExactEscapeWire) (label known : Nat) (row : Equation) : Bool :=
  if w.side row.left = 0 then
    match shapeOf row.right with
    | some (.record fields) =>
      fields.all (fun row => decide (row.1 ≠ label ∨ row.2 = known))
    | _ => true
  else true

structure ExactRecordVisitWire427 where
  root : ExactEscapeWire
  payload : ExactEscapeWire

def checkExactRecordVisits427 (s : GeneralDeclarativeHead320.State) (root label known : Nat)
    (w : ExactRecordVisitWire427) : Bool :=
  (checkExactEscape s root w.root && checkExactEscape s known w.payload) &&
    s.equations.all (oneQueriedField427 w.root label known)

theorem actual_same_label_field_is_exact427 {s root label known w}
    (checked : checkExactRecordVisits427 s root label known w = true)
    {fields : List (Nat × Nat)} {child : Nat}
    (reading : structural s root (.record fields)) (entry : (label,child) ∈ fields) :
    child = known := by
  have safe := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1
  have rows := (Bool.and_eq_true_iff.mp checked).2
  have root0 : w.root.side root = 0 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp safe).1).2
  obtain ⟨source,alias,code,present,decoded⟩ := reading
  have source0 := (exact_escape_preserves_alias_side410 safe alias).symm.trans root0
  have tested := List.all_eq_true.mp rows _ present
  have all : fields.all (fun row => decide (row.1 ≠ label ∨ row.2 = known)) = true := by
    simpa [oneQueriedField427,source0,decoded] using tested
  have here : label ≠ label ∨ child = known := of_decide_eq_true (List.all_eq_true.mp all _ entry)
  exact here.resolve_left (fun false => false rfl)

private theorem empty_primitive_visit427 {s : GeneralDeclarativeHead320.State} {ctor root site}
    (v : Visit (structural s) root (.primitive ctor []) site) : site = root := by
  cases v with
  | here => rfl
  | primitive _ bad _ _ => simp at bad

private theorem nested_binder_only_root427 {s : GeneralDeclarativeHead320.State} {tick binder root site}
    (v : Visit (structural s) root
      (.record tick (.variable binder) (.primitive .emptyRecord [])) site) : site = root := by
  cases v with
  | here => rfl
  | field _ _ clause inside =>
    have entry := Prod.mk.inj (List.mem_singleton.mp (by simpa [fieldPatterns] using clause))
    rw [entry.2] at inside
    exact False.elim (variable_has_no_visit inside)

/-- Exhaustive *raw visitation* for the two literal C15 head shapes,
without filtering the graph through fitted models or output support.
A nested captured variable is not a visited constructor. The closed
empty tail is not a named record payload in Visit. -/
theorem literal_record_candidate_visits_only_original_root_or_field427 {s root label known w part site}
    (checked : checkExactRecordVisits427 s root label known w = true)
    (shape : part = .primitive (.scalar .int) [] ∨
      ∃ tick binder, part = .record tick (.variable binder) (.primitive .emptyRecord []))
    (v : Visit (structural s) root (.record label part (.primitive .emptyRecord [])) site) :
    site = root ∨ site = known := by
  cases v with
  | here => exact .inl rfl
  | field lookup present key visit =>
    have eq := Prod.mk.inj (List.mem_singleton.mp (by simpa [fieldPatterns] using key))
    obtain ⟨keySame,partSame⟩ := eq
    rw [keySame] at present
    rw [partSame] at visit
    have child := actual_same_label_field_is_exact427 checked lookup present
    rcases shape with rfl|⟨_,_,rfl⟩
    · exact .inr ((empty_primitive_visit427 visit).trans child)
    · exact .inr ((nested_binder_only_root427 visit).trans child)

theorem checked_literal_record_candidate_preserves_raw_K2_priority427 {s root label known w part}
    (checked : checkExactRecordVisits427 s root label known w = true)
    (shape : part = .primitive (.scalar .int) [] ∨
      ∃ tick binder, part = .record tick (.variable binder) (.primitive .emptyRecord [])) :
    ¬ PatternK2 s root (.record label part (.primitive .emptyRecord [])) := by
  rintro ⟨site,visited,cycle⟩
  have ranks := (Bool.and_eq_true_iff.mp checked).1
  rcases literal_record_candidate_visits_only_original_root_or_field427 checked shape visited with h|h
  · rw [h] at cycle
    exact exact_escape_refutes_raw_root_K2410 ((Bool.and_eq_true_iff.mp ranks).1) cycle
  · rw [h] at cycle
    exact exact_escape_refutes_raw_root_K2410 ((Bool.and_eq_true_iff.mp ranks).2) cycle

/-- A successful same-state scan covers every literal candidate, not
just whichever positive read happened to run first. -/
def supportedVisitPart427 : Expr → Bool
  | .primitive (.scalar .int) [] => true
  | .record _ (.variable _) (.primitive .emptyRecord []) => true
  | _ => false

theorem checked_visit_part_exact427 {part : Expr} (ok : supportedVisitPart427 part = true) :
    part = .primitive (.scalar .int) [] ∨
    ∃ tick binder, part = .record tick (.variable binder) (.primitive .emptyRecord []) := by
  unfold supportedVisitPart427 at ok
  split at ok
  next => exact .inl rfl
  next tick binder => exact .inr ⟨tick,binder,rfl⟩
  next => contradiction

def checkedCandidateVisitBySource427 (s : State) (label : Nat) (d : GeneralDeclarations.Declaration) : Bool :=
  match d.head with
  | [p] =>
    match translateWhere427 s p with
    | some (.record actual part (.primitive .emptyRecord [])) =>
      decide (actual = label) && supportedVisitPart427 part
    | _ => false
  | _ => false

theorem checked_candidate_by_source_visits_exact427 {s root label known w d}
    (raw : checkExactRecordVisits427 s.current.ordinary root label known w = true)
    (read : checkedCandidateVisitBySource427 s label d = true) :
    ∃ p code, d.head = [p] ∧ translateWhere427 s p = some code ∧
      ¬ PatternK2 s.current.ordinary root code := by
  unfold checkedCandidateVisitBySource427 at read
  split at read
  next p head =>
    split at read
    next actual part code =>
      obtain ⟨labelHere,inside⟩ := Bool.and_eq_true_iff.mp read
      have eq : actual = label := of_decide_eq_true labelHere
      subst actual
      exact ⟨p,_,head,code,checked_literal_record_candidate_preserves_raw_K2_priority427 raw
        (checked_visit_part_exact427 inside)⟩
    next => contradiction
  next => contradiction

def checkWholePairRawVisits427 {s q} (p : ReadPositivePair427 s q)
    (parent child : ExactRecordVisitWire427) : Bool :=
  let a := p.parentRival.found
  let b := p.childRival.found
  (checkExactRecordVisits427 s.current.ordinary a.root a.box a.field parent &&
   checkExactRecordVisits427 s.current.ordinary b.root b.box b.field child) &&
  ((visible s q).all (checkedCandidateVisitBySource427 s a.box) &&
   (visible s p.original.child).all (checkedCandidateVisitBySource427 s b.box))

theorem whole_pair_preserves_original_raw_K2_for_both_complete_candidate_lists427 {s q p parent child}
    (ok : checkWholePairRawVisits427 (s:=s) (q:=q) p parent child = true) :
    (∀ d ∈ visible s q, ∃ source code, d.head = [source] ∧ translateWhere427 s source = some code ∧
      ¬ PatternK2 s.current.ordinary p.parentRival.found.root code) ∧
    (∀ d ∈ visible s p.original.child, ∃ source code, d.head = [source] ∧
      translateWhere427 s source = some code ∧
      ¬ PatternK2 s.current.ordinary p.childRival.found.root code) := by
  have watches := (Bool.and_eq_true_iff.mp ok).1
  have original := (Bool.and_eq_true_iff.mp ok).2
  exact ⟨fun d h => checked_candidate_by_source_visits_exact427
    ((Bool.and_eq_true_iff.mp watches).1) (List.all_eq_true.mp ((Bool.and_eq_true_iff.mp original).1) d h),
    fun d h => checked_candidate_by_source_visits_exact427
      ((Bool.and_eq_true_iff.mp watches).2) (List.all_eq_true.mp ((Bool.and_eq_true_iff.mp original).2) d h)⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere427
