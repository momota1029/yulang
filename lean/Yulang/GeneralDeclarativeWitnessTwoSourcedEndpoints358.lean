import Yulang.GeneralDeclarativeWitnessSharedTailProjection358
import Yulang.GeneralNominalStructuralProjectionLaws

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTwoSourcedEndpoints358
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessSharedTailProjection358 (field)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype subtype_trans record)
open PresenceNormalForm (Atom)

structure Window where
  label : Nat
  argument : Capture
  lowField : Nat
  highField : Nat
  lowRest : Nat
  highRest : Nat

def lowerRow (w : Window) := field w.argument.lower w.label w.lowField w.lowRest
def upperRow (w : Window) := field w.argument.upper w.label w.highField w.highRest
def left (w : Window) : Atom Nat := .tyLe (.var w.argument.lower) (.var w.argument.center)
def right (w : Window) : Atom Nat := .tyLe (.var w.argument.center) (.var w.argument.upper)

structure Read (source : Source) (current : State) (w : Window) : Prop where
  authored : lowerRow w ∈ source.authored ∧ upperRow w ∈ source.authored
  retained : lowerRow w ∈ current.equations ∧ upperRow w ∈ current.equations
  ordered : left w ∈ current.normal.ordinary ∧ right w ∈ current.normal.ordinary

def check (source : Source) (current : State) (w : Window) : Bool :=
  decide ((lowerRow w ∈ source.authored ∧ upperRow w ∈ source.authored) ∧
    (lowerRow w ∈ current.equations ∧ upperRow w ∈ current.equations) ∧
    (left w ∈ current.normal.ordinary ∧ right w ∈ current.normal.ordinary))

theorem check_exact {source current w} : check source current w = true ↔ Read source current w := by
  simp only [check,decide_eq_true_eq]
  exact ⟨fun q => ⟨q.1,q.2.1,q.2.2⟩,fun q => ⟨q.authored,q.retained,q.ordered⟩⟩

/-- Source-backed nonpoint record projection, with no hypothesis that the
center exposes any authored shape, and no choice of a center payload.
The original typed outer center lies between the two written forms. -/
theorem independently_sourced {source current w} (seen : Read source current w)
    (m : Assignment) (fits : Models current m) :
    Equivalent (m w.argument.lower).1 (record w.label (m w.lowField).1 (m w.lowRest).1) ∧
    Equivalent (m w.argument.upper).1 (record w.label (m w.highField).1 (m w.highRest).1) ∧
    Subtype (record w.label (m w.lowField).1 (m w.lowRest).1) (m w.argument.center).1 ∧
    Subtype (m w.argument.center).1 (record w.label (m w.highField).1 (m w.highRest).1) ∧
    Subtype (m w.lowField).1 (m w.highField).1 := by
  have lower : Equivalent (m w.argument.lower).1 (record w.label (m w.lowField).1 (m w.lowRest).1) :=
    fits.2 _ seen.retained.1
  have upper : Equivalent (m w.argument.upper).1 (record w.label (m w.highField).1 (m w.highRest).1) :=
    fits.2 _ seen.retained.2
  have lo : Subtype (record w.label (m w.lowField).1 (m w.lowRest).1) (m w.argument.center).1 :=
    subtype_trans lower.2 (fits.1.1 (left w) seen.ordered.1)
  have hi : Subtype (m w.argument.center).1 (record w.label (m w.highField).1 (m w.highRest).1) :=
    subtype_trans (fits.1.1 (right w) seen.ordered.2) upper.1
  exact ⟨lower,upper,lo,hi,GeneralNominalStructuralProjectionLaws.record_payload _ _ _ _ _
    (subtype_trans lo hi)⟩

end Yulang.GeneralDeclarativeWitnessTwoSourcedEndpoints358
