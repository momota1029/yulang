import Yulang.GeneralDeclarativeWitnessRootDeclared357
import Yulang.GeneralDeclarativeWitnessFullIntervals357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthoredProjection358
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessDeclaredState357 (Current centerEq)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans variant_congr union_congr eqv_refl)
open CommonNominalFullCarrier (Equivalent Subtype variant)
open PresenceNormalForm (Atom)

def tagged (slot tag payload : Nat) : Equation := ⟨slot,.variant tag (.variable payload)⟩

structure Source where
  authored : List Equation

structure Recipe where
  tag : Nat
  first : Nat
  last : Nat
  firstPayload : Nat
  lastPayload : Nat
  outer : Capture
  inner : Capture

def originated (r : Recipe) : List Equation :=
  [tagged r.first r.tag r.firstPayload,tagged r.last r.tag r.lastPayload,
   centerEq r.outer.center r.first r.last,
   centerEq r.inner.lower r.firstPayload r.lastPayload,
   centerEq r.inner.center r.firstPayload r.lastPayload,
   centerEq r.inner.upper r.firstPayload r.lastPayload]

def links (a : Capture) : List (Atom Nat) :=
  [.tyLe (.var a.lower) (.var a.center),.tyLe (.var a.center) (.var a.lower),
   .tyLe (.var a.center) (.var a.upper),.tyLe (.var a.upper) (.var a.center)]

structure Projected (author : Source) (s : State) (r : Recipe) : Prop where
  apart : r.first ≠ r.last
  nonpoint : r.outer.lower ≠ r.outer.center ∧ r.outer.center ≠ r.outer.upper
  authored : ∀ row ∈ originated r,row ∈ author.authored
  current : ∀ row ∈ originated r,row ∈ s.equations
  axes : ∀ a ∈ links r.outer,a ∈ s.normal.ordinary

def check (a : Source) (s : State) (r : Recipe) : Bool :=
  (decide (r.first ≠ r.last ∧ r.outer.lower ≠ r.outer.center ∧ r.outer.center ≠ r.outer.upper) &&
    (originated r).all (fun row => decide (row ∈ a.authored)) &&
    (originated r).all (fun row => decide (row ∈ s.equations))) &&
  (links r.outer).all (fun row => decide (row ∈ s.normal.ordinary))

theorem check_exact {author s r} : check author s r = true ↔ Projected author s r := by
  constructor
  · intro h
    obtain ⟨source,axes⟩ := GeneralDeclarativeWitnessProblem349.splitAnd h
    obtain ⟨initial,current⟩ := GeneralDeclarativeWitnessProblem349.splitAnd source
    obtain ⟨places,authored⟩ := GeneralDeclarativeWitnessProblem349.splitAnd initial
    obtain ⟨different,distinct⟩ := of_decide_eq_true places
    exact ⟨different,distinct,fun row inRow => of_decide_eq_true (List.all_eq_true.mp authored row inRow),
      fun row inRow => of_decide_eq_true (List.all_eq_true.mp current row inRow),
      fun row inRow => of_decide_eq_true (List.all_eq_true.mp axes row inRow)⟩
  · intro q
    unfold check
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
    exact ⟨⟨⟨⟨q.apart,q.nonpoint⟩,q.authored⟩,q.current⟩,q.axes⟩

def BoundsIn (m : Assignment) (r : Recipe) : Prop :=
  Equivalent (m r.outer.lower).1 (variant r.tag (m r.inner.lower).1) ∧
  Equivalent (m r.outer.center).1 (variant r.tag (m r.inner.center).1) ∧
  Equivalent (m r.outer.upper).1 (variant r.tag (m r.inner.upper).1) ∧
  Equivalent (m r.inner.lower).1 (.union (m r.firstPayload).1 (m r.lastPayload).1) ∧
  Equivalent (m r.inner.center).1 (.union (m r.firstPayload).1 (m r.lastPayload).1) ∧
  Equivalent (m r.inner.upper).1 (.union (m r.firstPayload).1 (m r.lastPayload).1)

theorem original_nonpoint_projection {a s r} (read : Projected a s r)
    (m : Assignment) (fit : Models s m) : BoundsIn m r := by
  have first : Equivalent (m r.first).1 (variant r.tag (m r.firstPayload).1) :=
    fit.2 (tagged r.first r.tag r.firstPayload) (read.current _ (by simp [originated]))
  have last : Equivalent (m r.last).1 (variant r.tag (m r.lastPayload).1) :=
    fit.2 (tagged r.last r.tag r.lastPayload) (read.current _ (by simp [originated]))
  have center : Equivalent (m r.outer.center).1 (.union (m r.first).1 (m r.last).1) :=
    fit.2 (centerEq r.outer.center r.first r.last) (read.current _ (by simp [originated]))
  have gathered := eqv_trans center (eqv_trans (union_congr first last)
    (variant_merge r.tag (m r.firstPayload).1 (m r.lastPayload).1))
  have low : Equivalent (m r.outer.lower).1 (m r.outer.center).1 :=
    ⟨fit.1.1 _ (read.axes (.tyLe (.var r.outer.lower) (.var r.outer.center)) (by simp [links])),
     fit.1.1 _ (read.axes (.tyLe (.var r.outer.center) (.var r.outer.lower)) (by simp [links]))⟩
  have high : Equivalent (m r.outer.upper).1 (m r.outer.center).1 :=
    ⟨fit.1.1 _ (read.axes (.tyLe (.var r.outer.upper) (.var r.outer.center)) (by simp [links])),
     fit.1.1 _ (read.axes (.tyLe (.var r.outer.center) (.var r.outer.upper)) (by simp [links]))⟩
  have whole {slot} (ok : centerEq slot r.firstPayload r.lastPayload ∈ originated r) :
      Equivalent (m slot).1 (.union (m r.firstPayload).1 (m r.lastPayload).1) :=
    fit.2 _ (read.current _ ok)
  have l := whole (slot := r.inner.lower) (by simp [originated])
  have c := whole (slot := r.inner.center) (by simp [originated])
  have u := whole (slot := r.inner.upper) (by simp [originated])
  refine ⟨?_,?_,?_,l,c,u⟩
  · exact eqv_trans low (eqv_trans gathered (variant_congr r.tag ⟨l.2,l.1⟩))
  · exact eqv_trans gathered (variant_congr r.tag ⟨c.2,c.1⟩)
  · exact eqv_trans high (eqv_trans gathered (variant_congr r.tag ⟨u.2,u.1⟩))

end Yulang.GeneralDeclarativeWitnessAuthoredProjection358
