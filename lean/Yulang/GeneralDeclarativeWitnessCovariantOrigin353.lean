import Yulang.GeneralDeclarativeWitnessCovariantMetadata353
import Yulang.CommonNominalRegularErasure
import Yulang.GeneralDeclarativeWitnessCompiler350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantOrigin353
open GeneralDeclarativeWitnessCovariantMetadata353 (Input Checked table table_key)
open GeneralDeclarativeWitnessCovariantHead352 (JoinedHead joinedHead)
open GeneralDeclarativeWitnessCovariant352 (Arm Plan merge unary)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalRegularErasure (layer subtype_monotone)
open Core.PresenceGeneration (Comp TyTerm)

structure Row where
  root : Nat
  tag : Nat
  box : Nat
  valueName : Nat
  deriving DecidableEq

/-- An independently supplied typed source extension. Old ordinary
equations do not acquire a nominal interpretation; the companion rows
have their own declared-variance semantics at their exact source names. -/
structure Problem where
  metadata : Input
  stage : State
  rows : List Row
  demand : Demand
  keep : List Nat
  fallback : Nat → Capture
  targets : GeneralDeclarations.Clause → Nat → Nat

def assigned (m : Assignment) (n : Nat) : Comp Common.model := (layer (m n).1,(m n).2)

def Row.asArm (r : Row) : Arm Nat := ⟨r.tag,unary r.box (.var r.valueName)⟩

structure View where
  tag : Nat
  box : Nat
  payload : Common.Ty

abbrev Valuation := Nat → Option View

def HasView (m : Assignment) (v : Valuation) (r : Row) : Prop :=
  ∃ atRoot : View, v r.root = some atRoot ∧ atRoot.tag = r.tag ∧ atRoot.box = r.box ∧
    Common.Equivalent atRoot.payload (assigned m r.valueName).1

def ModelsAt (p : Problem) (m : Assignment) (v : Valuation) : Prop :=
  Models p.stage m ∧ ∀ r ∈ p.rows, HasView m v r

def bill (combined first last : Nat) : Equation :=
  ⟨combined,.join (.variable first) (.variable last)⟩

def decListed (s : State) (e : Equation) : Bool := decide (e ∈ s.equations)

structure Wire where
  box : Nat
  written : Pattern
  left : Nat
  right : Nat
  center : Nat

structure Anchored (p : Problem) (w : Wire) where
  metadataProof : Checked p.metadata w.box
  shape : JoinedHead (table w.box) w.written
  sameBox : shape.box = w.box
  arg : Capture
  point : arg.lower = arg.center ∧ arg.upper = arg.center
  genuineDemand : p.demand.arguments = [arg]
  first : Row
  last : Row
  current : Row
  firstAt : p.rows[w.left]? = some first
  lastAt : p.rows[w.right]? = some last
  currentAt : p.rows[w.center]? = some current
  firstShape : first.tag = shape.tag ∧ first.box = shape.box
  lastShape : last.tag = shape.tag ∧ last.box = shape.box
  currentShape : current.tag = shape.tag ∧ current.box = shape.box
  actualCenter : current.root = arg.center
  equation : bill current.valueName first.valueName last.valueName ∈ p.stage.equations

def read (p : Problem) (w : Wire) : Option (Anchored p w) := do
  let m ← GeneralDeclarativeWitnessCovariantMetadata353.check p.metadata w.box
  let h ← joinedHead (table w.box) w.written
  if box : h.box = w.box then
    if decide (p.rows.map Row.root).Nodup && decide (w.left ≠ w.right ∧ w.left ≠ w.center ∧ w.right ≠ w.center) then
      match xs : p.demand.arguments with
      | [arg] =>
        if point : arg.lower = arg.center ∧ arg.upper = arg.center then
          match f : p.rows[w.left]?, l : p.rows[w.right]?, g : p.rows[w.center]? with
          | some first,some last,some current =>
            if fs : first.tag = h.tag ∧ first.box = h.box then
              if ls : last.tag = h.tag ∧ last.box = h.box then
                if gs : current.tag = h.tag ∧ current.box = h.box then
                  if actual : current.root = arg.center then
                    if present : decListed p.stage (bill current.valueName first.valueName last.valueName) = true then
                      some ⟨m,h,box,arg,point,xs,first,last,current,f,l,g,fs,ls,gs,actual,of_decide_eq_true present⟩
                    else none
                  else none
                else none
              else none
            else none
          | _,_,_ => none
        else none
      | _ => none
    else none
  else none

theorem whole_full {p : Problem} {w : Wire} (a : Anchored p w)
    (m : Assignment) (fit : Models p.stage m) :
    CommonNominalFullCarrier.Equivalent (m a.current.valueName).1
      (.union (m a.first.valueName).1 (m a.last.valueName).1) :=
  fit.2 _ a.equation

theorem whole_common {p : Problem} {w : Wire} (a : Anchored p w)
    (m : Assignment) (fit : Models p.stage m) :
    Common.Equivalent (assigned m a.current.valueName).1
      (.union (assigned m a.first.valueName).1 (assigned m a.last.valueName).1) := by
  have h := whole_full a m fit
  exact ⟨subtype_monotone _ _ h.1,subtype_monotone _ _ h.2⟩

theorem actual_center {p : Problem} {w : Wire} (a : Anchored p w)
    (m : Assignment) (v : Valuation) (fit : ModelsAt p m v) :
    ∃ selected : View, v a.arg.center = some selected ∧ selected.tag = a.shape.tag ∧
      selected.box = a.shape.box ∧ Common.Equivalent selected.payload
        (.union (assigned m a.first.valueName).1 (assigned m a.last.valueName).1) := by
  obtain ⟨chosen,key,tag,box,payload⟩ := fit.2 a.current (List.mem_iff_getElem?.mpr ⟨w.center,a.currentAt⟩)
  rw [a.actualCenter] at key
  have h := whole_common a m fit.1
  exact ⟨chosen,key,tag.trans a.currentShape.1,box.trans a.currentShape.2,
    Common.subtype_trans payload.1 h.1,Common.subtype_trans h.2 payload.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantOrigin353
