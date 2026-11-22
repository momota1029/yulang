import Yulang.GeneralDeclarativeCompoundOpenReceipt338
import Yulang.GeneralDeclarativeCompoundReadback338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpenReceipt339
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read interp)
open GeneralDeclarativeEndpointProgram336 (Projection)
open GeneralDeclarativeEndpointBatch336 (atSlots)
open GeneralDeclarativeEndpointOverlay336 (Entry Agreement)
open GeneralDeclarativeExactOverlay337 (Holds eval)
open GeneralDeclarativeExactDelete337 (subtract congruent)
open GeneralDeclarativeExactDeleteAuth337 (canonical)
open GeneralDeclarativeRecordSpine330 (ends was_named)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeCompoundOpenPrefix338 (residuals authorized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent)
open CommonRoleCanonicalRows (normalize residual)

/-- Value-side result indexed by the actual argument and the exact
projection address. No ordinary row is synthesized from an open tail. -/
def receipt (m : Assignment) (arg : GeneralDeclarativeWhere319.Capture)
    (keys : List Nat) (out : GeneralDeclarativeWhere319.Capture) : Prop :=
  Agreement (atSlots m out) (residuals keys m arg)

theorem same_open_endpoint {s : State} {p : Supported s done}
    (printed : Read p arg keys ls us first last le ue)
    (openRead : GeneralDeclarativeCompoundOpenPrefix338.Read p arg keys front back low high lterm uterm)
    (m : Assignment) (fit : Models s m) :
    Equivalent (interp m (withTail front lterm)) (interp m (withTail ls le)) ∧
      Equivalent (interp m (withTail back uterm)) (interp m (withTail us ue)) := by
  exact ⟨eqv_trans (eqv_symm (authorized openRead.anchors.1 m fit))
      (semantic (was_named printed.lo) m fit),
    eqv_trans (eqv_symm (authorized openRead.anchors.2 m fit))
      (semantic (was_named printed.hi) m fit)⟩

theorem endpoints {s : State} {p : Supported s done}
    (printed : Read p arg keys ls us first last le ue) (m : Assignment) (fit : Models s m) :
    Equivalent (residuals keys m arg).1 (interp m (withTail (residual keys (normalize ls)) le)) ∧
      Equivalent (residuals keys m arg).2.2 (interp m (withTail (residual keys (normalize us)) ue)) :=
  ⟨eqv_trans (congruent keys (semantic (was_named printed.lo) m fit))
      (canonical keys m ls (ends printed.lo)),
   eqv_trans (congruent keys (semantic (was_named printed.hi) m fit))
      (canonical keys m us (ends printed.hi))⟩

theorem as_values {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m : Assignment) (fit : Models s m)
    (out : GeneralDeclarativeWhere319.Capture) :
    Holds m (⟨.rest arg keys (withTail (residual keys (normalize ls)) le)
       (withTail (residual keys (normalize us)) ue),out⟩ : Entry) ↔ receipt m arg keys out := by
  obtain ⟨lo,hi⟩ := endpoints r m fit
  let old := (interp m (withTail (residual keys (normalize ls)) le),
    subtract keys (m arg.center).1,interp m (withTail (residual keys (normalize us)) ue))
  constructor
  · rintro ⟨x,found,agrees⟩
    have eq : old = x := Option.some.inj found
    subst x
    exact ⟨eqv_trans agrees.1 (eqv_symm lo),agrees.2.1,eqv_trans agrees.2.2 (eqv_symm hi)⟩
  · intro says
    exact ⟨old,rfl,eqv_trans says.1 lo,says.2.1,eqv_trans says.2.2 hi⟩

/-- A single actual allocated residual result satisfies either read
presentation in every model. This leaves literal compiler addresses
and all other jobs unchanged. -/
theorem routed {s : State} {p : Supported s done}
    (t : GeneralDeclarativeCompoundBatch338.Ticket p arg fs)
    (part : e ∈ GeneralDeclarativeCompoundBatch338.minted s old keep t.jobs)
    (rest : GeneralDeclarativeCompoundRoutes338.key e.1 = none)
    (m : Assignment) (fit : Models s m) :
    Holds m e ↔ receipt m arg (GeneralDeclarativeCompoundPattern338.layout fs |>.map Prod.fst) e.2 := by
  rcases GeneralDeclarativeCompoundReadback338.actual_recipe t part with ⟨k,a,b,isField,_,_⟩|isRest
  · rw [isField] at rest
    cases rest
  · obtain ⟨program,out⟩ := e
    change program = _ at isRest
    subst program
    exact as_values t.read m fit out

end Yulang.GeneralDeclarativeOpenReceipt339
