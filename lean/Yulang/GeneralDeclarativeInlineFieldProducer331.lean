import Yulang.GeneralDeclarativeInlineNegative331
import Yulang.GeneralDeclarativeInlineCompiler331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineFieldProducer331
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineTrace331 (Read Fields)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeInlineCompiler331 (Source)
open GeneralDeclarativeInlineExact331 (fixed_record_tail)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open GeneralDeclarativeRecordConsumption330 (lookup_iff)
open GeneralDeclarativeRecordPayloads330 (Field)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row lookup normalize_unique lookup_normalize)

abbrev Labels := List (Nat × Nat)

def keys (wanted : Labels) : List Nat := wanted.map Prod.fst
def codes (wanted : Labels) : Row Expr := wanted.map (fun v => (v.1,.variable v.2))
def actualUses : Mode → Labels → Row Expr → List Occurrence
  | mode,(_,key)::rest,(_,rhs)::later => ⟨key,mode,rhs⟩::actualUses mode rest later
  | _,_,_ => []

theorem field_coverage {s : State} (wanted : Labels) (seen : Row Expr)
    (same : keys wanted = seen.map Prod.fst) (mode : Mode) :
    Fields s mode seen (codes wanted) (actualUses mode wanted seen) := by
  induction wanted generalizing seen with
  | nil =>
    cases seen with
    | nil => exact .nil
    | cons item tail => cases same
  | cons top tail ih =>
    cases seen with
    | nil => cases same
    | cons first rest =>
      obtain ⟨key,binder⟩ := top
      obtain ⟨label,payload⟩ := first
      change key :: keys tail = label :: rest.map Prod.fst at same
      have headSame := (List.cons.inj same).1
      have restSame := (List.cons.inj same).2
      subst label
      exact .cons .capture (ih rest restSame)

theorem order_exists (raw : Row Expr) (selected : List Nat)
    (all : ∀ k ∈ selected, ∃ field, lookup k raw = some field) :
    ∃ used, order raw selected = some used := by
  induction selected with
  | nil => exact ⟨[],rfl⟩
  | cons k more ih =>
    obtain ⟨payload,has⟩ := all k List.mem_cons_self
    obtain ⟨picked,done⟩ := ih (fun key on => all key (List.mem_cons_of_mem _ on))
    exact ⟨(k,payload)::picked,by simp [order,has,done]⟩

/-- Produce all field witnesses for an arbitrary finite binder head
from the actual closed source and its visible labels. No field
trace, proposed output, or satisfying model is a premise. -/
theorem raw_head {s : State} (actual : Closed s term raw terminal) (wanted : Labels)
    (unique : (keys wanted).Nodup) (nonempty : keys wanted ≠ [])
    (visible : ∀ k ∈ keys wanted, ∃ e, Field k raw e) (mode : Mode) (tailBinder : Nat) :
    ∃ selected, order (CommonRoleCanonicalRows.normalize raw) (keys wanted) = some selected ∧
      Read s mode term (withTail (codes wanted) (.variable tailBinder))
        (actualUses mode wanted selected ++ [⟨tailBinder,mode,tailExpr raw (keys wanted) terminal⟩]) := by
  have assembled := order_exists (CommonRoleCanonicalRows.normalize raw) (keys wanted)
    (fun k needed => by
      obtain ⟨v,member⟩ := visible k needed
      exact ⟨v,(lookup_normalize raw k).trans (lookup_iff.mp member)⟩)
  obtain ⟨picked,out⟩ := assembled
  have observed := field_coverage (s := s) wanted picked
    ((exact_order (normalize_unique raw) out).1.symm) mode
  exact ⟨picked,out,fixed_record_tail actual unique nonempty out observed⟩

theorem independent_endpoints {s : State} (box : Bounds s arg)
    (lo : Closed s (.variable arg.lower) lower lowerTerm)
    (hi : Closed s (.variable arg.upper) upper upperTerm)
    (wanted : Labels) (unique : (keys wanted).Nodup) (nonempty : keys wanted ≠ [])
    (left : ∀ k ∈ keys wanted, ∃ e, Field k lower e)
    (right : ∀ k ∈ keys wanted, ∃ e, Field k upper e)
    (printed : translate c i (normalize pat) = some (withTail (codes wanted) (.variable binder))) :
    Matches s c i arg pat := by
  obtain ⟨_,_,l⟩ := raw_head lo wanted unique nonempty left .lower binder
  obtain ⟨_,_,u⟩ := raw_head hi wanted unique nonempty right .upper binder
  exact ⟨box,_,_,_,printed,l,u⟩

/-- Selection-time source production reads the centre, separately.
This single actual binder-record node can join an arbitrary
independently sourced tail of the head argument list. -/
theorem independent_actual {s : State} {p : Supported s done} (box : Bounds s arg)
    (actual : Closed (restriction p) (.variable arg.center) raw terminal)
    (wanted : Labels) (unique : (keys wanted).Nodup) (nonempty : keys wanted ≠ [])
    (visible : ∀ k ∈ keys wanted, ∃ e, Field k raw e)
    (printed : translate c i (normalize pat) = some (withTail (codes wanted) (.variable binder)))
    (tail : Source p c i arguments patterns) :
    Source p c i (arg::arguments) (pat::patterns) := by
  obtain ⟨_,_,read⟩ := raw_head actual wanted unique nonempty visible .actual binder
  exact .inline box printed read tail

end Yulang.GeneralDeclarativeInlineFieldProducer331
