import Yulang.GeneralDeclarativeWitnessPointModes357
import Yulang.GeneralDeclarativeWitnessCovariantHead352
import Yulang.GeneralDeclarativeWitnessCompiler350
import Yulang.GeneralDeclarativeOutputRequests323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessDeclaredState357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute fixed_targets)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonNominalFullCarrier (Ty Equivalent)
open CommonNominalConstraints (ArgumentTerm)
open CommonDeclaredNominalInspection (Parameter)

structure AuthoredNominal where
  place : Nat
  tag : Nat
  name : Nat
  arguments : List (ArgumentTerm Nat)

structure Current where
  environment : Environment
  ordinary : State
  visible : List AuthoredNominal

/-- The new model keeps ordinary assignment and independent declared
nominal observations together. Neither coerces arbitrary nominal values
into legacy invariant semantics. -/
structure Value where
  tag : Nat
  name : Nat
  arguments : List (Ty ⊕ Common.Row)
abbrev Views := Nat → Option Value

def evaluate (m : Assignment) : ArgumentTerm Nat → Ty ⊕ Common.Row
  | .value t => .inl (t.eval CommonNominalFullCarrier.model m)
  | .row t => .inr (t.eval CommonNominalFullCarrier.model m)

def Seen (m : Assignment) (v : Views) (row : AuthoredNominal) : Prop :=
  ∃ a : Value, v row.place = some a ∧ a.tag = row.tag ∧ a.name = row.name ∧
    a.arguments = row.arguments.map (evaluate m)

def ModelsCurrent (s : Current) (m : Assignment) (v : Views) : Prop :=
  Models s.ordinary m ∧ ∀ row ∈ s.visible,Seen m v row

def observed (root tag name payload : Nat) : AuthoredNominal :=
  ⟨root,tag,name,[.value (.var payload)]⟩

def centerEq (slot left right : Nat) : Equation :=
  ⟨slot,.join (.variable left) (.variable right)⟩

def point (slot : Nat) : Capture := ⟨slot,slot,slot⟩

def pointSpans (x y slot : Nat) : List (Nat × Capture) := [(x,point slot),(y,point slot)]

/-- Declarative source conditions for the approved unary covariant
same-tag join, not assumptions about a successful solver or old Coverage. -/
structure Joined (s : Current) (d : Demand) (impl : Declaration) where
  tag : Nat
  name : Nat
  firstBinder : Nat
  lastBinder : Nat
  different : firstBinder ≠ lastBinder
  written : Pattern
  head : impl.head = [written]
  normalized : normalize written =
    .variant tag (.join (.app name [.var firstBinder]) (.app name [.var lastBinder]))
  use : Use s.environment name 1
  co : use.mode = .declared [⟨.value,.covariant⟩]
  sourceFirst : Nat
  sourceLast : Nat
  actual : Nat
  firstValue : Nat
  lastValue : Nat
  actualValue : Nat
  demanded : d.arguments = [point actual]
  first : observed sourceFirst tag name firstValue ∈ s.visible
  last : observed sourceLast tag name lastValue ∈ s.visible
  center : observed actual tag name actualValue ∈ s.visible
  whole : centerEq actualValue firstValue lastValue ∈ s.ordinary.equations

theorem joined_values {s : Current} {d impl} (h : Joined s d impl)
    (m : Assignment) (v : Views) (fit : ModelsCurrent s m v) :
    (∃ a : Value, v h.actual = some a ∧ a.tag = h.tag ∧ a.name = h.name ∧
      a.arguments = [.inl (m h.actualValue).1]) ∧
    (∀ row ∈ pointSpans h.firstBinder h.lastBinder h.actualValue,
      Equivalent (m row.2.center).1 (.union (m h.firstValue).1 (m h.lastValue).1)) := by
  have val := fit.2 _ h.center
  have whole := fit.1.2 _ h.whole
  have first : ∃ a : Value, v h.actual = some a ∧ a.tag = h.tag ∧ a.name = h.name ∧
      a.arguments = [.inl (m h.actualValue).1] := val
  refine ⟨first,fun x here => ?_⟩
  simp only [pointSpans,List.mem_cons,List.not_mem_nil,or_false] at here
  rcases here with same|same <;> rw [same] <;> exact whole

def authoredRegistry (s : Current) := registry s.environment.source

def context (s : Current) (d : Demand) (impl : Declaration)
    (named : State) (spans : List (Nat × Capture)) (keep : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) : Context :=
  ⟨authoredRegistry s,interpretation s.environment.source.snapshot,d,impl,named,spans,keep,fallback,targets⟩

/-- Source body and current receipt. Body compiles *only the reached
fragment*, not every declared nominal pattern using old Coverage. -/
structure WrittenBody (s : Current) (d : Demand) (impl : Declaration)
    (spans : List (Nat × Capture)) (kids : List Demand) where
  named : State
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  finished : Finished
  run : execute (context s d impl named spans keep fallback targets) = some finished
  children : finished.kids = kids
  retained : Receipt finished.state s.ordinary

theorem output_meaning {s : Current} {d impl spans kids} (b : WrittenBody s d impl spans kids)
    (m : Assignment) (valid : Models s.ordinary m) :
    b.finished.fixed.map Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
    ∀ eq ∈ b.finished.fixed,Holds m eq :=
  ⟨fixed_targets b.run,((model_append m).mp (relays_models b.retained m valid)).2⟩

theorem emitted_declared {c : Context}
    (signature : c.decl.Signature c.registry.roles) {ports d}
    (member : d ∈ GeneralDeclarativeEmissionForest322.children c.decl
      (GeneralDeclarativeWitnessCompiler350.portNames c ports)
      (GeneralDeclarativeWitnessCompiler350.placed c ports)) : Declared c.registry d := by
  obtain ⟨clause,present,rfl⟩ := List.mem_map.mp member
  have legal := signature.2.2.2 clause present
  intro out requested
  unfold GeneralDeclarativeWitnessCompiler350.portNames GeneralDeclarativeWitnessCompiler350.placed at *
  rw [GeneralDeclarativeSourceEmission322.outputs_match_source c.decl clause legal] at requested
  exact (GeneralDeclarationDemands.childDemand c.decl clause legal _
    (GeneralDeclarativeEmissionErasure322.oldPlacement _ clause)).declared out requested

theorem execute_declared {c : Context} {f : Finished}
    (run : execute c = some f) (signature : c.decl.Signature c.registry.roles) :
    ∀ d ∈ f.kids,Declared c.registry d := by
  unfold execute at run
  cases prep : GeneralDeclarativeWitnessCompiler350.preparation c with
  | none => simp [prep] at run
  | some args =>
    rcases args with ⟨before,ports⟩
    cases whereRows : GeneralDeclarativeWitnessCompiler350.whereBatch c ports with
    | none => simp [prep,whereRows] at run
    | some whereRowsData =>
      cases rows : GeneralDeclarativeWitnessCompiler350.fixedBatch c ports with
      | none => simp [prep,whereRows,rows] at run
      | some fixed =>
        simp [prep,whereRows,rows] at run
        subst f
        exact fun _ here => emitted_declared signature here

theorem body_declared {s : Current} {d impl spans kids} (b : WrittenBody s d impl spans kids)
    (signature : impl.Signature (authoredRegistry s).roles) :
    ∀ child ∈ kids,Declared (authoredRegistry s) child := by
  rw [← b.children]
  exact execute_declared b.run signature

end Yulang.GeneralDeclarativeWitnessDeclaredState357
