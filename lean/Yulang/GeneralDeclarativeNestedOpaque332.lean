import Yulang.GeneralDeclarativeNestedTail332
import Yulang.GeneralDeclarativeNestedBracket332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedOpaque332
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedClash332 (pairExpr)
open GeneralDeclarativeNestedDecode332 (normalized)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedTail332 (withScripts)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source from_completed)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty exactEmpty record variant pair)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev exactStop : Expr := .primitive .exactEmpty []
abbrev tail := Expr.record 8 (.variable 12) (.variable 21)
abbrev rhs := Expr.variant 4 (pairExpr (.variable 3) (.record 7 (.variable 4) (.variable 20)))
abbrev rootRow : Equation := ⟨0,rhs⟩
abbrev middleRow : Equation := ⟨20,tail⟩
abbrev stopRow : Equation := ⟨21,exactStop⟩
abbrev eqs : List Equation := [rootRow,middleRow,stopRow]
abbrev state : State := ⟨⟨[],[]⟩,eqs⟩
abbrev target : Pattern := .variant 4 (.app 5 [.var 0,.record 7 (.var 1) (.var 2)])
abbrev remainder := Expr.record 8 (.variable 12) exactStop
abbrev seen : List Occurrence :=
  [⟨0,.actual,.variable 3⟩,⟨1,.actual,.variable 4⟩,⟨2,.actual,remainder⟩]

def done (first last : Bool) : Nat → Prop :=
  fun owner => (owner = 99 ∧ first = true) ∨ (owner = 100 ∧ last = true)

def support (first last : Bool) : Supported state (done first last) :=
  ⟨fun row origin => (row = rootRow ∧ origin = .source) ∨
    (row = middleRow ∧ origin = .output 99) ∨ (row = stopRow ∧ origin = .output 100),by
      rintro e o (⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

def visible (first last : Bool) : List Equation :=
  [rootRow] ++ (if first then [middleRow] else []) ++ (if last then [stopRow] else [])

theorem backed (first last : Bool) :
    visible first last ⊆ (restriction (support first last)).equations := by
  intro e used
  unfold visible at used
  rcases List.mem_append.mp used with earlier|ending
  · rcases List.mem_append.mp earlier with raw|middle
    · cases List.mem_singleton.mp raw
      exact from_source _ (.inl ⟨rfl,rfl⟩)
    · cases first <;> simp only [Bool.false_eq_true,ite_false,ite_true] at middle
      · cases middle
      · cases List.mem_singleton.mp middle
        exact from_completed _ (.inr (.inl ⟨rfl,rfl⟩)) (.inl ⟨rfl,rfl⟩)
  · cases last <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ending
    · cases ending
    · cases List.mem_singleton.mp ending
      exact from_completed _ (.inr (.inr ⟨rfl,rfl⟩)) (.inr ⟨rfl,rfl⟩)

noncomputable def source (first last : Bool) (endName : Nat) :=
  withScripts (ofRows (visible first last) (backed first last))
    (fun n => if n = 20 then some [endName] else none)

theorem actual_dependency (first last : Bool) :
    normalized (source first last 21) constructors interpretation .actual (.variable 0) target =
      if first && last then some seen else none := by
  cases first <;> cases last <;> rfl

theorem wrong_path :
    normalized (source true true 22) constructors interpretation .actual (.variable 0) target = none := rfl

abbrev bool : Ty := .base .bool
abbrev tailType := record 8 int exactEmpty
abbrev rootType := variant 4 (pair int (record 7 bool tailType))
def model : Assignment := fun n =>
  (if n = 0 then rootType else if n = 20 then tailType else if n = 21 then exactEmpty
    else if n = 4 then bool else int,Common.rowEmpty)

theorem ordinary_unchanged : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩,?_⟩
  intro row present
  change row ∈ eqs at present
  simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with h|h|h <;> cases h <;> exact eqv_refl _

end Yulang.GeneralDeclarativeNestedOpaque332
