import Yulang.GeneralDeclarativeClausePlacement327
import Yulang.GeneralDeclarativeNormalizeCovered322
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereOutputBatch327
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeClauseOrigins325 (Origin origin_here)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translate_complete)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralNominalInspection (Interpretation)

def alreadyNamed (impl : Declaration) (eq : GeneralDeclarations.Equation) : Bool :=
  match normalize eq.rhs with
  | .var n => impl.outputNames.contains n
  | _ => false

theorem direct_exact : alreadyNamed impl eq = true ↔ Direct impl eq := by
  unfold alreadyNamed Direct
  cases form : normalize eq.rhs with
  | var binder => simp
  | app tag args | record tag args _ | variant tag args | join tag args => simp

def entry (r : Registry) (i : Interpretation) (impl : Declaration) (names : Names)
    (targets : Nat → Nat) (eq : GeneralDeclarations.Equation) : Option (List Equation) := do
  let written ← translate r.constructors i (normalize eq.rhs)
  pure (if alreadyNamed impl eq then []
    else [⟨(useOutput impl names targets eq).target,logical names.input .actual written⟩])

def whole (r : Registry) (i : Interpretation) (impl : Declaration) (names : Names)
    (targets : Clause → Nat → Nat) : Option (List Equation) :=
  collect (fun cl => collect (entry r i impl names (targets cl)) cl.outputs) impl.requirements

theorem collect_exact {xs : List α} (success : collect f xs = some rows) :
    ∀ row, row ∈ rows ↔ ∃ a ∈ xs, ∃ own, f a = some own ∧ row ∈ own := by
  induction xs generalizing rows with
  | nil =>
    cases Option.some.inj success
    simp
  | cons a as ih =>
    cases one : f a with
    | none => simp [collect,one] at success
    | some before =>
      cases tail : collect f as with
      | none => simp [collect,one,tail] at success
      | some after =>
        have exact : before ++ after = rows := by simpa [collect,one,tail] using success
        subst rows
        intro row
        rw [List.mem_append,ih tail row]
        constructor
        · rintro (first|⟨there,member,own,listed,h⟩)
          · exact ⟨a,List.mem_cons_self,before,one,first⟩
          · exact ⟨there,List.mem_cons_of_mem _ member,own,listed,h⟩
        · rintro ⟨x,member,own,listed,hit⟩
          rcases List.mem_cons.mp member with rfl|other
          · cases Option.some.inj (one.symm.trans listed)
            exact .inl hit
          · exact .inr ⟨x,other,own,listed,hit⟩

theorem collect_total {xs : List α} (defined : ∀ a ∈ xs, ∃ own, f a = some own) :
    ∃ rows, collect f xs = some rows := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons a as ih =>
    obtain ⟨before,one⟩ := defined a List.mem_cons_self
    obtain ⟨after,tail⟩ := ih (fun b seen => defined b (List.mem_cons_of_mem _ seen))
    exact ⟨before++after,by simp [collect,one,tail]⟩

theorem collect_defined {xs : List α} (built : collect f xs = some rows) :
    ∀ a ∈ xs, ∃ own, f a = some own := by
  induction xs generalizing rows with
  | nil => intro x found; cases found
  | cons a xs ih =>
    cases one : f a with
    | none => simp [collect,one] at built
    | some first =>
      cases later : collect f xs with
      | none => simp [collect,one,later] at built
      | some rest =>
        intro x wanted
        rcases List.mem_cons.mp wanted with rfl|there
        · exact ⟨first,one⟩
        · exact ih later x there

theorem compiled (covered : Coverage r i) (visible : impl ∈ r.declarations) :
    ∃ rows, whole r i impl names targets = some rows := by
  apply collect_total
  intro cl found
  apply collect_total
  intro eq wanted
  obtain ⟨written,known⟩ := translate_complete (normalize_covered (((covered.1 impl visible).2.1 cl found).2 eq wanted))
  exact ⟨_,by rw [entry,known]; rfl⟩

/-- Applying the actual independent normalized where-output source
batch yields exactly the requested rows; direct output binders do not
get a redundant defining row. These are ordinary constraints and
can narrow the existing models, unlike fresh input naming. -/
theorem exact {rows : List Equation} (finished : whole r i impl names targets = some rows) :
    ∀ row, row ∈ rows ↔ ∃ cl ∈ impl.requirements, ∃ eq ∈ cl.outputs, ¬Direct impl eq ∧
      ∃ written, translate r.constructors i (normalize eq.rhs) = some written ∧
      row = ⟨(useOutput impl names (targets cl) eq).target,logical names.input .actual written⟩ := by
  intro row
  constructor
  · intro found
    obtain ⟨cl,used,requestRows,fromClause,there⟩ := (collect_exact finished row).mp found
    obtain ⟨eq,wanted,own,defined,inside⟩ := (collect_exact fromClause row).mp there
    cases decoding : translate r.constructors i (normalize eq.rhs) with
    | none => simp [entry,decoding] at defined
    | some value =>
      by_cases usedBinder : alreadyNamed impl eq = true
      · have empty : own = [] := by simpa [entry,decoding,usedBinder,eq_comm] using defined
        exact False.elim (List.not_mem_nil (empty ▸ inside))
      · have final : own = [⟨(useOutput impl names (targets cl) eq).target,logical names.input .actual value⟩] := by
          simpa [entry,decoding,usedBinder,eq_comm] using defined
        exact ⟨cl,used,eq,wanted,fun direct => usedBinder (direct_exact.mpr direct),
          value,decoding,List.mem_singleton.mp (final ▸ inside)⟩
  · rintro ⟨cl,used,eq,wanted,nondirect,value,decoding,rfl⟩
    unfold whole at finished
    obtain ⟨requestRows,there⟩ := collect_defined finished cl used
    have notNamed : alreadyNamed impl eq ≠ true := fun yes => nondirect (direct_exact.mp yes)
    refine (collect_exact finished _).mpr ⟨cl,used,requestRows,there,?_⟩
    let wantedRow : Equation := ⟨(useOutput impl names (targets cl) eq).target,logical names.input .actual value⟩
    have well : entry r i impl names (targets cl) eq = some [wantedRow] := by simp [entry,decoding,notNamed,wantedRow]
    exact (collect_exact there _).mpr ⟨eq,wanted,[wantedRow],well,List.mem_cons_self⟩

theorem origin_after {s : State} (covered : Coverage r i) (visible : impl ∈ r.declarations)
    (finished : whole r i impl names targets = some rows)
    (included : cl ∈ impl.requirements) (request : eq ∈ cl.outputs) :
    ∃ written, translate r.constructors i (normalize eq.rhs) = some written ∧
      (¬Direct impl eq → Origin (appendFacts s rows) (useOutput impl names (targets cl) eq).target
        (logical names.input .actual written)) := by
  obtain ⟨written,known⟩ := translate_complete
    (normalize_covered (((covered.1 impl visible).2.1 cl included).2 eq request))
  exact ⟨written,known,fun guard => origin_here (List.mem_append_right _
    ((exact finished _).mpr ⟨cl,included,eq,request,guard,written,known,rfl⟩))⟩

end Yulang.GeneralDeclarativeWhereOutputBatch327
