import Yulang.GeneralWhereOriginDelta318
import Yulang.GeneralWherePhysicalDeferred319

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereRawExpr346
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterialization (Mode)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedExpressionFrame236 (variableSource variable_value)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralSourceState (State)
open Core.PresenceGeneration (TyTerm)

/-- Exact physical encoding of structurally expressible materialized
input expressions. It is partial: native nominal values are tracked
by descriptor storage, not represented by a forged TyTerm. -/
def compile (locate : Nat → Option (Fin n)) (expr : Expr) : Option (TyTerm (Fin n)) :=
  match expr with
  | .variable name => (locate name).map TyTerm.var
  | .primitive (.scalar k) [] => some (.base k)
  | .primitive .emptyRecord [] => some .emptyRecord
  | .primitive .exactEmpty [] => some .exactEmpty
  | .primitive .pair [x,y] => (compile locate x).bind (fun a => (compile locate y).map (TyTerm.pair a))
  | .record label payload tail => (compile locate payload).bind (fun a => (compile locate tail).map (TyTerm.record label a))
  | .variant tag payload => (compile locate payload).map (TyTerm.variant tag)
  | .join first last => (compile locate first).bind (fun a => (compile locate last).map (TyTerm.union a))
  | _ => none

theorem value_exact {p : Plan rs} (s : State) (mode : Mode) (e : Expr)
    {term : TyTerm (Fin s.slots)}
    (found : compile (fun name => sourceSlot s (variableSource p mode name)) e = some term)
    (m : Assignment) :
    term.eval CommonNominalFullCarrier.model (assignment s m) = value (variables p m) mode e := by
  cases e with
  | «variable» name =>
    obtain ⟨i,located,rfl⟩ := Option.map_eq_some_iff.mp found
    change (m (s.source i)).1 = variables p m mode name
    rw [variable_value,(sourceSlot_exact ..).mp located]
  | primitive constructor args =>
    cases constructor with
    | scalar k =>
      cases args with
      | nil => cases found; rfl
      | cons => cases found
    | emptyRecord =>
      cases args with
      | nil => cases found; rfl
      | cons => cases found
    | exactEmpty =>
      cases args with
      | nil => cases found; rfl
      | cons => cases found
    | pair =>
      cases args with
      | nil => cases found
      | cons x more =>
        cases more with
        | nil => cases found
        | cons y tail =>
          cases tail with
          | cons => cases found
          | nil =>
            cases a : compile (fun n => sourceSlot s (variableSource p mode n)) x <;>
              cases b : compile (fun n => sourceSlot s (variableSource p mode n)) y <;>
              simp [compile,a,b] at found
            subst term
            simp only [TyTerm.eval,value,GeneralNominalCenteredHeadMatExpressions.values,
              GeneralNominalCenteredHeadMatExpressions.primitiveValue]
            rw [value_exact s mode _ a m,value_exact s mode _ b m]
            rfl
  | nominal _ _ => cases found
  | record label payload tail =>
    cases a : compile (fun n => sourceSlot s (variableSource p mode n)) payload <;>
      cases b : compile (fun n => sourceSlot s (variableSource p mode n)) tail <;>
      simp [compile,a,b] at found
    subst term
    simp only [TyTerm.eval,value]
    rw [value_exact s mode _ a m,value_exact s mode _ b m]
    rfl
  | variant tag payload =>
    cases a : compile (fun n => sourceSlot s (variableSource p mode n)) payload <;>
      simp [compile,a] at found
    subst term
    simp only [TyTerm.eval,value]
    rw [value_exact s mode _ a m]
    rfl
  | join x y =>
    cases a : compile (fun n => sourceSlot s (variableSource p mode n)) x <;>
      cases b : compile (fun n => sourceSlot s (variableSource p mode n)) y <;>
      simp [compile,a,b] at found
    subst term
    simp only [TyTerm.eval,value]
    rw [value_exact s mode _ a m,value_exact s mode _ b m]
    rfl
termination_by sizeOf e
decreasing_by all_goals subst_vars; simp_wf; omega

end Yulang.GeneralDeclarativeWhereRawExpr346
