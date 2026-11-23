import Yulang.GeneralDeclarativeWitnessRecordSpine359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordResidual359
open CommonNominalFullCarrier (Ty Equivalent Subtype record subtype_trans)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessTwoSourcedEndpoints358 (Window left right)
open GeneralDeclarativeExactDeleteRigid337 (literal surviving interval)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeWitnessRecordSpine359 (Spine)
open GeneralNominalCommonBridge (Assignment)

structure Receipt where
  window : Window
  lower : Spine
  upper : Spine

def lowerSpine (r : Receipt) : Spine :=
  .cons r.window.label r.window.lowField r.window.lowRest r.lower
def upperSpine (r : Receipt) : Spine :=
  .cons r.window.label r.window.highField r.window.highRest r.upper

structure Read (source : Source) (current : State) (r : Receipt) : Prop where
  lower : GeneralDeclarativeWitnessRecordSpine359.Read source current r.window.argument.lower (lowerSpine r)
  upper : GeneralDeclarativeWitnessRecordSpine359.Read source current r.window.argument.upper (upperSpine r)
  ordered : left r.window ∈ current.normal.ordinary ∧ right r.window ∈ current.normal.ordinary

def check (source : Source) (current : State) (r : Receipt) : Bool :=
  GeneralDeclarativeWitnessRecordSpine359.check source current r.window.argument.lower (lowerSpine r) &&
  GeneralDeclarativeWitnessRecordSpine359.check source current r.window.argument.upper (upperSpine r) &&
  decide (left r.window ∈ current.normal.ordinary ∧ right r.window ∈ current.normal.ordinary)

theorem check_exact {source current r} : check source current r = true ↔ Read source current r := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,GeneralDeclarativeWitnessRecordSpine359.check_exact]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun e => ⟨⟨e.lower,e.upper⟩,e.ordered⟩⟩

def after (sp : Spine) (keys : List Nat) (m : Assignment) : Ty :=
  literal (surviving keys (sp.fields m)) sp.kind.ty

/-- Projection and subtraction of an inherited interval, not selection.
Absolute named input center is unchanged; no center expression is used. -/
theorem authored_interval {source current r} (read : Read source current r)
    (m : Assignment) (fit : Models current m) :
    Equivalent (m r.window.argument.lower).1 ((lowerSpine r).denote m) ∧
    Equivalent (m r.window.argument.upper).1 ((upperSpine r).denote m) ∧
    Subtype (m r.window.lowField).1 (m r.window.highField).1 ∧
    ∀ keys, Subtype (after (lowerSpine r) keys m) (subtract keys (m r.window.argument.center).1) ∧
      Subtype (subtract keys (m r.window.argument.center).1) (after (upperSpine r) keys m) := by
  have lo := GeneralDeclarativeWitnessRecordSpine359.read_in_model read.lower m fit
  have hi := GeneralDeclarativeWitnessRecordSpine359.read_in_model read.upper m fit
  have lower := subtype_trans lo.2 (fit.1.1 (left r.window) read.ordered.1)
  have upper := subtype_trans (fit.1.1 (right r.window) read.ordered.2) hi.1
  have all := subtype_trans lower upper
  have narrow := GeneralNominalStructuralProjectionLaws.record_payload r.window.label
    (m r.window.lowField).1 (m r.window.highField).1 (r.lower.denote m) (r.upper.denote m) all
  refine ⟨lo,hi,narrow,fun keys => ?_⟩
  exact interval keys ((lowerSpine r).fields m) ((upperSpine r).fields m)
    (lowerSpine r).kind.terminal (upperSpine r).kind.terminal ⟨lower,upper⟩

end Yulang.GeneralDeclarativeWitnessRecordResidual359
