import Yulang.GeneralNominalReportSourceTransport
import Yulang.GeneralNominalReportErasure

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalReportCoordinates305
open GeneralNominalState (State)
open GeneralNominalInspection (Bounds Query)
open GeneralNormalizedObservation (Shape)
open GeneralNominalRecursiveInspection
open GeneralNominalReportSourceTransport (moveBounds moveReport)

inductive HeadData (slots : Type) where
  | pending
  | scalar (base : Inference.Base)
  | structural (shape : Shape) (children : List slots)

def observed (s : State) (i : Fin s.base.slots) : HeadData (Fin s.base.slots) :=
  match s.view.heads i with
  | .deferred _ => .pending
  | .scalar base => .scalar base
  | .structural k children => .structural (s.view.shapes k) (List.ofFn children)

def nominalRead (s : State) (i : Fin s.base.slots) : Option (Nat × Option (List (Bounds s))) :=
  (s.nominals i).map (fun d => (d.declaration.name,typeArguments d.arguments))

def HeadData.move (f : α → β) : HeadData α → HeadData β
  | .pending => .pending
  | .scalar base => .scalar base
  | .structural shape children => .structural shape (children.map f)

def nominalMove {a b : State} (f : Fin a.base.slots → Fin b.base.slots) :
    Option (Nat × Option (List (Bounds a))) → Option (Nat × Option (List (Bounds b))) :=
  Option.map fun (name,arguments) => (name,arguments.map (List.map (moveBounds f)))

/-- Exactly the facts read by the inspection program. The target can have a
different shape catalogue, including entries never used by an observed head. -/
structure Coordinates (a b : State) where
  slot : Fin a.base.slots → Fin b.base.slots
  source_eq : ∀ i, b.base.source (slot i) = a.base.source i
  normalized : ∀ i, observed b (slot i) = (observed a i).move slot
  nominal : ∀ i, nominalRead b (slot i) = nominalMove slot (nominalRead a i)

theorem Coordinates.injective (rel : Coordinates a b) : Function.Injective rel.slot := by
  intro i j h
  apply a.base.source_injective
  exact (rel.source_eq i).symm.trans ((congrArg b.base.source h).trans (rel.source_eq j))

def scalarMiss {s : State} (span : Bounds s) (expected : Inference.Base) :
    HeadData (Fin s.base.slots) → Report s
  | .pending => block span
  | .scalar actual => if expected = actual then {} else {conflicts := [span]}
  | .structural _ _ => {conflicts := [span]}

def nodeBody (s : State) (span : Bounds s) (origin : Option Origin) (expected : Shape)
    (patterns : List Query) : HeadData (Fin s.base.slots) → HeadData (Fin s.base.slots) → Report s
  | .structural l children,.structural r targets =>
    if l = expected ∧ r = expected then
      inspectMany s patterns (children.zip targets)
        (fun index => origin.map fun parent => .structural parent expected index) 0
    else block span
  | .scalar _,_ => {conflicts := [span]}
  | _,_ => block span

def nominalBody (s : State) (span : Bounds s) (origin : Option Origin) (expected : Nat)
    (patterns : List Query) :
    Option (Nat × Option (List (Bounds s))) → Option (Nat × Option (List (Bounds s))) →
    HeadData (Fin s.base.slots) → Report s
  | none,_,.pending => block span
  | none,_,_ => {conflicts := [span]}
  | some (name,args),upper,_ =>
    if name = expected then
      match args with
      | none => block span
      | some arguments =>
        let left := inspectMany s patterns arguments
          (fun index => some (.nominal (origin.getD (.source (s.base.source span.1))) expected index)) 0
        if span.1 = span.2 then left
        else match upper with
        | none => block span
        | some (other,more) => if other = expected then
          match more with
          | none => block span
          | some targets => left.append (inspectMany s patterns targets
            (fun index => some (.nominal (origin.getD (.source (s.base.source span.2))) expected index)) 0)
          else {conflicts := [span]}
    else {conflicts := [span]}

theorem scalar_equation (s : State) (span : Bounds s) (origin : Option Origin) (kind : Inference.Base) :
    inspect s (.scalar kind) span origin = Report.visit span origin (.scalar kind)
      (if (nominalRead s span.1).isSome then {conflicts := [span]}
       else scalarMiss span kind (observed s span.1)) := by
  simp only [inspect]
  congr 1
  unfold nominalRead observed
  cases s.nominals span.1 <;> cases s.view.heads span.1 <;> rfl

theorem node_equation (s : State) (span : Bounds s) (origin : Option Origin) (shape : Shape)
    (patterns : List Query) :
    inspect s (.node shape patterns) span origin = Report.visit span origin (.structural shape)
      (nodeBody s span origin shape patterns (observed s span.1) (observed s span.2)) := by
  simp only [inspect]
  congr 1
  unfold observed
  cases s.view.heads span.1 <;> cases s.view.heads span.2 <;> rfl

theorem nominal_equation (s : State) (span : Bounds s) (origin : Option Origin) (name : Nat)
    (patterns : List Query) :
    inspect s (.nominal name patterns) span origin = Report.visit span origin (.nominal name patterns.length)
      (nominalBody s span origin name patterns (nominalRead s span.1) (nominalRead s span.2)
        (observed s span.1)) := by
  simp only [inspect]
  congr 1
  unfold nominalRead observed
  cases s.nominals span.1 with
  | none => cases s.nominals span.2 <;> cases s.view.heads span.1 <;> rfl
  | some lower => cases s.nominals span.2 <;> rfl

end Yulang.GeneralNominalReportCoordinates305
