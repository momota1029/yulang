import Yulang.GeneralDeclarativeWitnessCovariantJoin353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantInterval353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row View Valuation HasView assigned)
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared prepare)
open GeneralDeclarativeWitnessCovariantViews353 (View.head actual_box_order)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeWitnessBound349 (Path)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeWitnessCompiler350 (Context Accepted printDemand)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open CommonNominalRegularErasure (subtype_monotone)

def pointAt (p : Problem) (center : Nat) : Problem :=
  {p with demand := {p.demand with arguments := [⟨center,center,center⟩]}}

structure Wire where
  center : GeneralDeclarativeWitnessCovariantOrigin353.Wire
  low : Nat
  high : Nat
  lowerBound : Path
  upperBound : Path

structure RangeRead (p : Problem) (w : Wire) where
  arg : Capture
  shape : p.demand.arguments = [arg]
  center : Prepared (pointAt p arg.center) w.center
  lower : Row
  upper : Row
  fromLower : p.rows[w.low]? = some lower
  fromUpper : p.rows[w.high]? = some upper
  lowerAt : lower.root = arg.lower
  upperAt : upper.root = arg.upper
  lowerShape : lower.tag = center.anchor.shape.tag ∧ lower.box = w.center.box
  upperShape : upper.tag = center.anchor.shape.tag ∧ upper.box = w.center.box
  lowerVerified : Bound p.stage.normal lower.valueName center.anchor.current.valueName
  upperVerified : Bound p.stage.normal center.anchor.current.valueName upper.valueName

def read (p : Problem) (w : Wire) : Option (RangeRead p w) :=
  match actual : p.demand.arguments with
  | [arg] => do
    let a ← prepare (pointAt p arg.center) w.center
    match lo : p.rows[w.low]?, hi : p.rows[w.high]? with
    | some l,some u =>
      if low : l.root = arg.lower ∧ l.tag = a.anchor.shape.tag ∧ l.box = w.center.box then
        if high : u.root = arg.upper ∧ u.tag = a.anchor.shape.tag ∧ u.box = w.center.box then
          if lowOK : GeneralDeclarativeWitnessBound349.check p.stage l.valueName a.anchor.current.valueName w.lowerBound = true then
            if highOK : GeneralDeclarativeWitnessBound349.check p.stage a.anchor.current.valueName u.valueName w.upperBound = true then
              some ⟨arg,actual,a,l,u,lo,hi,low.1,high.1,low.2,high.2,
                GeneralDeclarativeWitnessBound349.sound lowOK,GeneralDeclarativeWitnessBound349.sound highOK⟩
            else none
          else none
        else none
      else none
    | _,_ => none
  | _ => none

theorem actual_index {p : Problem} {w : Wire} (a : RangeRead p w) :
    a.center.anchor.arg.center = a.arg.center := by
  have h := a.center.anchor.genuineDemand
  change [({lower:=a.arg.center,center:=a.arg.center,upper:=a.arg.center} : Capture)] = [a.center.anchor.arg] at h
  have adjusted := congrArg Capture.center (List.cons.inj h).1.symm
  exact adjusted

theorem typed_interval {p : Problem} {w : Wire} (a : RangeRead p w)
    (m : Assignment) (v : Valuation) (fit : Models p.stage m) (actual : ∀ r ∈ p.rows, HasView m v r) :
    ∃ lo center hi : View,
      v a.arg.lower = some lo ∧ v a.arg.center = some center ∧ v a.arg.upper = some hi ∧
      Common.Equivalent center.payload
        (.union (assigned m a.center.anchor.first.valueName).1 (assigned m a.center.anchor.last.valueName).1) ∧
      DeclaredSubtype (table w.center.box) (View.head lo) (View.head center) ∧
      DeclaredSubtype (table w.center.box) (View.head center) (View.head hi) := by
  obtain ⟨l,lo,_,lb,lp⟩ := actual a.lower (List.mem_iff_getElem?.mpr ⟨_,a.fromLower⟩)
  obtain ⟨u,hi,_,ub,up⟩ := actual a.upper (List.mem_iff_getElem?.mpr ⟨_,a.fromUpper⟩)
  obtain ⟨c,here,_,cb,whole⟩ := GeneralDeclarativeWitnessCovariantOrigin353.actual_center
    a.center.anchor m v ⟨fit,actual⟩
  obtain ⟨cc,found,_,_,cp⟩ := actual a.center.anchor.current (List.mem_iff_getElem?.mpr ⟨_,a.center.anchor.currentAt⟩)
  rw [a.lowerAt] at lo
  rw [a.upperAt] at hi
  rw [actual_index a] at here
  rw [a.center.anchor.actualCenter,actual_index a,here] at found
  cases Option.some.inj found
  have lEdge := subtype_monotone _ _ (bound_sound m fit.1 a.lowerVerified)
  have hEdge := subtype_monotone _ _ (bound_sound m fit.1 a.upperVerified)
  have key := cb.trans a.center.anchor.sameBox
  refine ⟨l,c,u,lo,here,hi,whole,?_,?_⟩
  · exact actual_box_order l c _ (lb.trans a.lowerShape.2) key
      (Common.subtype_trans lp.1 (Common.subtype_trans lEdge cp.2))
  · exact actual_box_order c u _ key (ub.trans a.upperShape.2)
      (Common.subtype_trans cp.1 (Common.subtype_trans hEdge up.2))

def RangeRead.ctx {p : Problem} {w : Wire} (a : RangeRead p w) : Context :=
  {a.center.ctx with demand := p.demand}

structure Checked (p : Problem) (w : Wire) (s : State) (out : GeneralDeclarativeWitnessCompiler350.Wire) where
  facts : RangeRead p w
  kept : preserves p.stage s = true
  compiler : Accepted facts.ctx s out

def decode (p : Problem) (w : Wire) (s : State) (out : GeneralDeclarativeWitnessCompiler350.Wire) :
    Option (Checked p w s out) := do
  let facts ← read p w
  if kept : preserves p.stage s = true then do
    let compiler ← GeneralDeclarativeWitnessCompiler350.decode facts.ctx s out
    pure ⟨facts,kept,compiler⟩
  else none

theorem exact_write_targets {p : Problem} {w : Wire} {s : State} {out}
    (a : Checked p w s out) (m : Assignment) (fit : Models s m) :
    out.children = a.compiler.compiled.kids.map printDemand ∧
    out.outputRows.map Equation.left = p.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ e ∈ out.outputRows,Holds m e :=
  ⟨a.compiler.printed,GeneralDeclarativeWitnessCompiler350.fixed_in_current a.compiler m fit⟩

end Yulang.GeneralDeclarativeWitnessCovariantInterval353
