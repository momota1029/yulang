import Yulang.GeneralNominalCaptureMerges
import Yulang.GeneralNominalMixedRecurrence

/-! Finite pattern-directed inspection of interval endpoints. Captures retain
actual nominal and structural projection paths. No whole descendant cone is
inspected for a variable pattern, and no nominal body is traversed. -/
namespace Yulang.GeneralNominalRecursiveInspection

open GeneralNominalState (State)
open GeneralNominalInspection (Query Bounds Interpretation queries)
open GeneralNormalizedObservation (Shape)
open CommonNominalFullCarrier

inductive Origin where
  | source (identity : Nat)
  | nominal (parent : Origin) (name index : Nat)
  | structural (parent : Origin) (shape : Shape) (index : Nat)
  deriving DecidableEq

def shapeValue (shape : Shape) (values : List Ty) : Ty :=
  (shape.term (fun index : Fin shape.arity => index)).eval CommonNominalFullCarrier.model
    (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty))

inductive Observes (model : GeneralNominalCommonBridge.Assignment) : Origin → Ty → Prop
  | source (identity) : Observes model (.source identity) (model identity).1
  | nominal : Observes model parent value → Equivalent value (nominal name arguments) →
      arguments[index]? = some (.inl actual) → Observes model (.nominal parent name index) actual
  | structural : Observes model parent value → values.length = shape.arity →
      Equivalent value (shapeValue shape values) → values[index]? = some actual →
      Observes model (.structural parent shape index) actual

def embed : GeneralNominalProjections.Ref → Origin
  | .source identity => .source identity
  | .argument parent name index => .nominal (embed parent) name index

theorem embed_observation (model : GeneralNominalCommonBridge.Assignment)
    (ref : GeneralNominalProjections.Ref) (actual : Ty)
    (seen : GeneralNominalProjections.Observes model ref (.inl actual)) :
    Observes model (embed ref) actual := by
  generalize valueEq : Sum.inl actual = value at seen
  induction seen generalizing actual with
  | source identity => cases valueEq; exact .source identity
  | argument parent equal found ih =>
      cases valueEq
      exact .nominal (ih _ rfl) equal found

theorem recover_observation (model : GeneralNominalCommonBridge.Assignment)
    (ref : GeneralNominalProjections.Ref) (actual : Ty)
    (seen : Observes model (embed ref) actual) : GeneralNominalProjections.Observes model ref (.inl actual) := by
  induction ref generalizing actual with
  | source identity => cases seen; exact .source identity
  | argument parent name index ih =>
      cases seen with
      | nominal seen equal found => exact .argument (ih _ seen) equal found

theorem nominal_observation_unique (model : GeneralNominalCommonBridge.Assignment)
    (ref : GeneralNominalProjections.Ref) (first last : Ty)
    (one : Observes model (embed ref) first) (two : Observes model (embed ref) last) : Equivalent first last :=
  GeneralNominalProjections.observation_unique model ref (.inl first) (.inl last)
    (recover_observation model ref first one) (recover_observation model ref last two)

theorem nominal_argument_bounds (state : State) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (index : Nat) (bounds : Bounds state) (found : descriptor.arguments[index]? = some (.type bounds)) :
    (∃ actual, Observes model (.nominal (.source (state.base.source slot)) descriptor.declaration.name index) actual) ∧
      ∀ actual, Observes model (.nominal (.source (state.base.source slot)) descriptor.declaration.name index) actual →
        GeneralNominalCaptureMerges.Fits model (state.base.source bounds.1,state.base.source bounds.2) actual := by
  obtain ⟨value,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid state model models slot descriptor recorded index 0 (.type bounds) found
  cases value with
  | inr => cases fits
  | inl value =>
      have observed := embed_observation model _ value seen
      refine ⟨⟨value,observed⟩,?_⟩
      intro actual present
      have equal := nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name index)
        value actual observed present
      exact ⟨subtype_trans fits.1 equal.1,subtype_trans equal.2 fits.2⟩

structure Capture (state : State) where
  name : Nat
  bounds : Bounds state
  origin : Option Origin

inductive Test where
  | scalar (base : Inference.Base)
  | structural (shape : Shape)
  | nominal (name arity : Nat)

def Test.Holds : Test → Ty → Prop
  | .scalar base, actual => Equivalent actual (.base base)
  | .structural shape, actual => ∃ values, values.length = shape.arity ∧ Equivalent actual (shapeValue shape values)
  | .nominal name arity, actual => ∃ arguments, arguments.length = arity ∧ Equivalent actual (CommonNominalFullCarrier.nominal name arguments)

structure Report (state : State) where
  captures : List (Capture state) := []
  inspected : List (Bounds state) := []
  checked : List (Bounds state) := []
  blocked : List (Bounds state) := []
  conflicts : List (Bounds state) := []
  arity : List (Nat × Nat) := []
  anchors : List (Origin × Bounds state) := []
  tests : List (Origin × Test) := []

def Report.append (first last : Report state) : Report state :=
  ⟨first.captures ++ last.captures,first.inspected ++ last.inspected,first.checked ++ last.checked,
    first.blocked ++ last.blocked,first.conflicts ++ last.conflicts,first.arity ++ last.arity,
    first.anchors ++ last.anchors,first.tests ++ last.tests⟩

def Report.visit (bounds : Bounds state) (origin : Option Origin) (test : Test) (report : Report state) : Report state :=
  { report with
    inspected := bounds :: report.inspected
    checked := bounds :: report.checked
    anchors := origin.toList.map (fun ref => (ref,bounds)) ++ report.anchors
    tests := origin.toList.map (fun ref => (ref,test)) ++ report.tests }

def block (bounds : Bounds state) : Report state := { blocked := [bounds] }

def typeArguments (arguments : List (GeneralNominalState.Parameter slots)) : Option (List (Fin slots × Fin slots)) :=
  arguments.mapM fun parameter => match parameter with | .type bounds => some bounds | .row _ => none

mutual
  def inspect (state : State) (query : Query) (bounds : Bounds state) (origin : Option Origin) : Report state :=
    match query with
    | .variables names =>
        { captures := names.map fun name => ⟨name,bounds,origin⟩, checked := [bounds],
          anchors := origin.toList.map fun ref => (ref,bounds) }
    | .deferred _ => block bounds
    | .scalar expected => Report.visit bounds origin (.scalar expected) <|
        match state.nominals bounds.1 with
        | some _ => { conflicts := [bounds] }
        | none => match state.view.heads bounds.1 with
          | .scalar actual => if expected = actual then {} else { conflicts := [bounds] }
          | .structural _ _ => { conflicts := [bounds] }
          | _ => block bounds
    | .node expected patterns => Report.visit bounds origin (.structural expected) <|
        match state.view.heads bounds.1,state.view.heads bounds.2 with
        | .structural lower children,.structural upper targets =>
            if state.view.shapes lower = expected ∧ state.view.shapes upper = expected then
              inspectMany state patterns ((List.ofFn children).zip (List.ofFn targets))
                (fun index => origin.map fun parent => .structural parent expected index) 0
            else block bounds
        | .scalar _,_ => { conflicts := [bounds] }
        | _,_ => block bounds
    | .nominal expected patterns => Report.visit bounds origin (.nominal expected patterns.length) <|
        match state.nominals bounds.1 with
        | none => match state.view.heads bounds.1 with
          | .scalar _ | .structural _ _ => { conflicts := [bounds] }
          | _ => block bounds
        | some lower =>
            if lower.declaration.name = expected then
              match typeArguments lower.arguments with
              | none => block bounds
              | some arguments =>
                  let left := inspectMany state patterns arguments
                    (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) expected index)) 0
                  if bounds.1 = bounds.2 then left
                  else match state.nominals bounds.2 with
                    | none => block bounds
                    | some upper =>
                        if upper.declaration.name = expected then
                          match typeArguments upper.arguments with
                          | none => block bounds
                          | some targets => left.append (inspectMany state patterns targets
                              (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.2))) expected index)) 0)
                        else { conflicts := [bounds] }
            else { conflicts := [bounds] }
  termination_by sizeOf query

  def inspectMany (state : State) : List Query → List (Bounds state) → (Nat → Option Origin) → Nat → Report state
    | [],[],_,_ => {}
    | pattern :: patterns,bounds :: intervals,origins,index =>
        (inspect state pattern bounds (origins index)).append (inspectMany state patterns intervals origins (index+1))
    | patterns,intervals,_,_ => { arity := [(patterns.length,intervals.length)] }
  termination_by patterns _ _ _ => sizeOf patterns
end

def bindings (state : State) (report : Report state) : GeneralNominalAllocation.Bindings :=
  report.captures.map fun capture =>
    (capture.name,state.base.source capture.bounds.1,state.base.source capture.bounds.2)

def selfChecks (state : State) (report : Report state) : List (PresenceNormalForm.Atom Nat) :=
  report.checked.map fun bounds => .tyLe (.var (state.base.source bounds.1)) (.var (state.base.source bounds.2))

def Fits (state : State) (model : GeneralNominalCommonBridge.Assignment) (bounds : Bounds state) (actual : Ty) : Prop :=
  GeneralNominalCaptureMerges.Fits model (state.base.source bounds.1,state.base.source bounds.2) actual

/-- Actual observations and their sharing are extra branch constraints. The
model still assigns the original source identities; captures contain intervals. -/
def ProjectionModels (state : State) (report : Report state) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  (∀ anchor ∈ report.anchors, (∃ actual, Observes model anchor.1 actual) ∧
    ∀ actual, Observes model anchor.1 actual → Fits state model anchor.2 actual) ∧
  (∀ test ∈ report.tests, ∀ actual, Observes model test.1 actual → test.2.Holds actual) ∧
  (∀ first ∈ report.captures, ∀ last ∈ report.captures, first.name = last.name →
    ∀ ref, first.origin = some ref → ∀ actual, Observes model ref actual → Fits state model last.bounds actual) ∧
  (∀ first ∈ report.captures, ∀ last ∈ report.captures, first.name = last.name →
    ∀ a b, first.origin = some a → last.origin = some b →
    ∀ x y, Observes model a x → Observes model b y → Equivalent x y)

def Finished (report : Report state) : Prop := report.blocked = [] ∧ report.conflicts = [] ∧ report.arity = []

theorem nonpoint_type_arguments (bounds : Fin slots × Fin slots) :
    typeArguments [.type bounds] = some [bounds] := rfl

theorem variable_does_not_inspect (state : State) (names : List Nat) (bounds : Bounds state) (origin : Option Origin) :
    (inspect state (.variables names) bounds origin).inspected = [] := by simp [inspect]

theorem unresolved_blocks (state : State) (expected : Nat) (patterns : List Query) (bounds : Bounds state)
    (origin : Option Origin) (nominal : state.nominals bounds.1 = none)
    (unknown : state.view.heads bounds.1 = .deferred .unresolved) :
    (inspect state (.nominal expected patterns) bounds origin).blocked ≠ [] := by
  simp [inspect,nominal,unknown,Report.visit,block]

theorem projected_capture_sound (state : State) (report : Report state)
    (model : GeneralNominalCommonBridge.Assignment) (models : ProjectionModels state report model)
    (first last : Capture state) (one : first ∈ report.captures) (two : last ∈ report.captures)
    (same : first.name = last.name) (origin : Origin) (source : first.origin = some origin)
    (actual : Ty) (seen : Observes model origin actual) : Fits state model last.bounds actual :=
  models.2.2.1 first one last two same origin source actual seen

end Yulang.GeneralNominalRecursiveInspection
