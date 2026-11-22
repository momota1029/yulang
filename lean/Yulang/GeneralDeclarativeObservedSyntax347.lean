import Yulang.GeneralDeclarativeNamedProjection347
import Yulang.GeneralDeclarativeStoppedStructural339
import Yulang.GeneralDeclarativeWhereNominal346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedSyntax347
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeStoppedStructural339 (encode meaning)
open GeneralStoppedShape335 (descriptorExpr descriptor_semantics)
open GeneralNormalizedObservation (Head)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Equivalent model)

def structural (s : State) (target : Nat) : Option Equation := do
  let i ← sourceSlot s.base target
  let term ← (s.view.heads i).term
  let code ← encode s.base term
  pure ⟨target,code⟩

def rawHead (s : State) (target : Nat) : Option Equation := do
  let i ← sourceSlot s.base target
  let term ← (s.base.heads i).equation
  let code ← encode s.base term
  pure ⟨target,code⟩

def nominalPoint (s : State) (target : Nat) : Option Equation := do
  let i ← sourceSlot s.base target
  let d ← s.nominals i
  let code ← descriptorExpr s.base d
  pure ⟨target,code⟩

theorem structural_exact {s : State} {target : Nat} {row : Equation} (h : structural s target = some row) :
    ∃ (i : Fin s.base.slots) (term : Core.PresenceGeneration.TyTerm (Fin s.base.slots)) (code : Expr), sourceSlot s.base target = some i ∧
      (s.view.heads i).term = some term ∧ encode s.base term = some code ∧ row = ⟨target,code⟩ := by
  unfold structural at h
  obtain ⟨i,slot,a⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨term,observed,b⟩ := Option.bind_eq_some_iff.mp a
  obtain ⟨code,encoded,c⟩ := Option.bind_eq_some_iff.mp b
  exact ⟨i,term,code,slot,observed,encoded,(Option.some.inj c).symm⟩

theorem structural_sound {s : State} {target : Nat} {row : Equation} (h : structural s target = some row)
    (m : Assignment) (fit : Models s m) : Holds m row := by
  obtain ⟨i,term,code,slot,observed,printed,rfl⟩ := structural_exact h
  have eq := GeneralNominalState.normalized_models s m fit i term observed
  change Equivalent (m (s.base.source i)).1 (term.eval model (assignment s.base m)) at eq
  rw [(sourceSlot_exact ..).mp slot,meaning s.base m term printed] at eq
  exact eq

theorem nominal_point_sound {s : State} {target : Nat} {row : Equation} (h : nominalPoint s target = some row)
    (m : Assignment) (fit : Models s m) : Holds m row := by
  unfold nominalPoint at h
  obtain ⟨i,slot,a⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d,recorded,b⟩ := Option.bind_eq_some_iff.mp a
  obtain ⟨code,encoded,c⟩ := Option.bind_eq_some_iff.mp b
  have eq := (descriptor_semantics s.base i d m encoded).mp (fit.2.1 i d recorded)
  rw [(sourceSlot_exact ..).mp slot] at eq
  exact (Option.some.inj c) ▸ eq

theorem raw_head_sound {s : State} {target : Nat} {row : Equation} (h : rawHead s target = some row)
    (m : Assignment) (fit : Models s m) : Holds m row := by
  unfold rawHead at h
  obtain ⟨i,slot,a⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨term,observed,b⟩ := Option.bind_eq_some_iff.mp a
  obtain ⟨code,encoded,c⟩ := Option.bind_eq_some_iff.mp b
  have eq := fit.1.2.1 i term observed
  rw [(sourceSlot_exact ..).mp slot,meaning s.base m term encoded] at eq
  exact (Option.some.inj c) ▸ eq

/-- These routes consult the current *stored normalized view*, not
merely an equation entailed by it. Nonpoint invariant descriptors are
represented by the nominal side table, never forced through this
point-only expression route. -/
inductive Appears (s : State) : Equation → Prop
  | structural : structural s target = some row → Appears s row
  | rawHead : rawHead s target = some row → Appears s row
  | nominalPoint : nominalPoint s target = some row → Appears s row

theorem holds {s : State} {row : Equation} (found : Appears s row) (m : Assignment) (fit : Models s m) :
    Holds m row := by
  cases found with
  | structural h => exact structural_sound h m fit
  | rawHead h => exact raw_head_sound h m fit
  | nominalPoint h => exact nominal_point_sound h m fit

end Yulang.GeneralDeclarativeObservedSyntax347
