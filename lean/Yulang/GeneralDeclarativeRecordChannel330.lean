import Yulang.GeneralDeclarativeOpaqueChannel328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
namespace Yulang.GeneralDeclarativeRecordChannel330
open CommonNominalFullCarrier (Ty Row observeTy)
open CommonNominalSyntax (graph)
open CommonNominalFullDemand (Observation Environment MaskedProbeStep)
open GeneralDeclarativeOpaqueChannel328 (union meet tests)

def channel (optional : Bool) (key : Nat) (obs : Observation Row) : Observation Row :=
  if optional then .optional key obs else .field key obs

def shows (key label : Nat) (hidden : List Nat) : Prop := key = label ∧ label ∉ hidden
instance (key label : Nat) (hidden : List Nat) : Decidable (shows key label hidden) := inferInstanceAs
  (Decidable (key = label ∧ label ∉ hidden))

def addTrivial (optional : Bool) (value : Option Ty) : Option Ty :=
  if optional then meet value (some .top) else value

def defaultField (optional : Option Ty) (required : Option Ty) (fallback : Ty) : Option Ty :=
  if required.isSome then optional else union optional (some fallback)

/-- Required and optional are separate channels. Tail and mask are
followed without fabricating a logical tail name. For defaults the
literal presence test is distinguished from the payload predicate. -/
def project (key : Nat) (optional : Bool) (hidden : List Nat) : Ty → Option Ty
  | .bottom => some .bottom
  | .emptyRecord => if optional then some .top else none
  | .exactEmpty => if optional then some (if key ∈ hidden then .top else .bottom) else none
  | .record label p t =>
    if shows key label hidden then some (graph Row p)
    else addTrivial optional (project key optional hidden t)
  | .recordDefault label t fallback =>
    addTrivial optional (if shows key label hidden then
      defaultField (project key true hidden t) (project key false hidden t) (graph Row fallback)
    else project key optional hidden t)
  | .mask names inner => project key optional (hidden ++ names) inner
  | .union a b => union (project key optional hidden a) (project key optional hidden b)
  | .inter a b => meet (project key optional hidden a) (project key optional hidden b)
  | _ => none

theorem test_some (d : Nat) (env : Environment Row) (order)
    (payload : Option Ty) : tests d env order .trivial payload ↔ payload.isSome = true := by
  cases payload with
  | none => simp [tests]
  | some a => cases h : observeTy d a <;> simp [tests,h,MaskedProbeStep]

theorem top_only (d : Nat) (env : Environment Row) (order) (obs : Observation Row) :
    tests d env order obs (some .top) ↔ obs = .trivial := by
  cases obs <;> simp [tests,observeTy,CommonNominalSyntax.Layer.evalAt,MaskedProbeStep]

theorem optional_extra (d : Nat) (env : Environment Row) (order) (obs : Observation Row)
    (optional : Bool) (payload : Option Ty) :
    tests d env order obs (addTrivial optional payload) ↔
      tests d env order obs payload ∨ optional = true ∧ obs = .trivial := by
  cases optional
  · simp [addTrivial]
  · simp only [addTrivial,ite_true,GeneralDeclarativeOpaqueChannel328.tests_meet,top_only,true_and]

theorem default_extra (d : Nat) (env : Environment Row) (order) (obs : Observation Row)
    (opt req : Option Ty) (fallback : Ty) :
    tests d env order obs (defaultField opt req fallback) ↔
      tests d env order obs opt ∧
        (tests d env order .trivial req ∨ tests d env order obs (some fallback)) := by
  cases req <;> simp [defaultField,test_some,GeneralDeclarativeOpaqueChannel328.tests_union]

end Yulang.GeneralDeclarativeRecordChannel330
