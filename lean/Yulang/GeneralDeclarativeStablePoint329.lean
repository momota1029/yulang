import Yulang.GeneralDeclarativeStableActual329
import Yulang.GeneralDeclarativeStableModels329
import Yulang.GeneralDeclarativeStableOrigin329

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeStablePoint329
open GeneralDeclarativeStableActual329 (SameActual by_name evidence)
open GeneralDeclarativeStableFixture329 (final inputRows)
open GeneralDeclarativeStableProbe329 (support safe)
open GeneralDeclarativeStableResult329 (dict branch every_model)
open GeneralDeclarativeStableModels329 (genuine assignment)
open GeneralDeclarativeNestedModels328 (payload)
open GeneralDeclarativeOpaqueFixture328 (oldRows)
open GeneralDeclarativeRepeatDecl327 (arg reg root interp)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOrigins321 (restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Knows Alias Delayed)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev point : Capture := ⟨1,1,1⟩
abbrev pointRoot : Demand := ⟨root.role,[point],root.outputs⟩

theorem same_actual (m) : SameActual m root pointRoot :=
  ⟨rfl,.cons (by_name rfl) .nil,.cons ⟨rfl,eqv_refl _⟩ .nil⟩

theorem same_dictionary (m) (fit : Models final m) : Evidence reg interp m pointRoot dict :=
  evidence m fit (same_actual m) (by
    intro a found
    cases List.mem_singleton.mp found
    exact ⟨.refl _,.refl _⟩) (every_model m fit)

theorem visible_when_incomplete {e : Equation}
    (present : e ∈ (restriction (support (fun _ => False))).equations) : e ∈ oldRows ++ inputRows := by
  obtain ⟨o,byOrigin,usable⟩ := (backed_iff _ _).mp present
  rcases byOrigin with (authored|⟨_,rfl⟩)|⟨_,rfl⟩
  · exact authored.1
  · cases usable with
    | completed impossible => exact False.elim impossible
  · cases usable with
    | completed impossible => exact False.elim impossible

def rank (n : Nat) := if n ≤ 2 then n else 3

theorem one_class {a b : Nat} (h : Alias (restriction (support (fun _ => False))) a b) :
    rank a = rank b := by
  have noVariable {x y : Nat} (present : (⟨x,.variable y⟩ : Equation) ∈ oldRows ++ inputRows) : False := by
    simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h|h|h|h <;> cases h
  have path {a b} (flow : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a ≤ rank b := by
    induction flow with
    | refl => exact Nat.le_refl _
    | interval stored =>
      change _ ∈ [(0,1),(1,2),(9,10),(10,11)] at stored
      simp only [List.mem_cons,List.not_mem_nil,or_false] at stored
      rcases stored with h|h|h|h <;> cases h <;> decide +kernel
    | constraint stored =>
      change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 3) (.var 7),.tyLe (.var 7) (.var 4),
        .tyLe (.var 3) (.var 8),.tyLe (.var 8) (.var 4)] at stored
      simp only [List.mem_cons,List.not_mem_nil,or_false] at stored
      rcases stored with h|h|h|h <;> cases h <;> decide +kernel
    | trans _ _ x y => exact Nat.le_trans x y
  induction h with
  | bounds one other => exact Nat.le_antisymm (path one) (path other)
  | forward row => exact False.elim (noVariable (visible_when_incomplete row))
  | backward row => exact False.elim (noVariable (visible_when_incomplete row))
  | trans _ _ h k => exact h.trans k

theorem lacks_support (label) :
    ¬Knows (restriction (support (fun _ => False))) point.lower label := by
  rintro ⟨row,present,bridge,_⟩
  have fromOld := visible_when_incomplete present
  have same := one_class bridge
  simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at fromOld
  rcases fromOld with x|x|x|x|x|x <;> cases x <;> cases same

theorem unsupported : Delayed (support (fun _ => False)) pointRoot :=
  ⟨point,List.mem_cons_self,lacks_support⟩

theorem raw_point_pending : branch (fun _ => False) pointRoot .pending :=
  .unsupported unsupported (safe (fun _ => False) pointRoot)

/-- The semantic sharing of input and fixed output does not create a
source origin for a point view. This is an uncoalesced diagnostic;
it is not an instruction to reject or postpone demands that the
language has already coalesced using its same-input rule. -/
theorem distinct :
    (¬Equivalent ((assignment payload payload) arg.lower).1 ((assignment payload payload) point.lower).1) ∧
    Models final (assignment payload payload) ∧
    Evidence reg interp (assignment payload payload) pointRoot dict ∧
    branch (fun _ => False) pointRoot .pending := by
  have model := genuine.2.1
  exact ⟨fun asEndpoints => genuine.2.2.2.1 (GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm asEndpoints),
    model,same_dictionary _ model,raw_point_pending⟩

end Yulang.GeneralDeclarativeStablePoint329
