import Yulang.GeneralNominalExpressionIntervals237
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 3600000
/-! I-56: a where-argument bridge over arbitrary declarative constraints and
intervals. Logical variables have no identity in the execution journal.
This does not choose a new source acceptance policy. -/
namespace Yulang.GeneralDeclarativeWhere319
open CommonNominalFullCarrier (Ty Row Subtype Equivalent subtype_trans model)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany value)
open GeneralNominalExpressionIntervals237 (reads interval)
open GeneralNominalCenteredHeadMatPatternSemantics (eval)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralDeclarations (Declaration Clause)
open PresenceNormalForm (Atom All)

structure State where
  ordinary : List (Atom Nat)
  intervals : List (Nat × Nat)

def Models (state : State) (m : Assignment) : Prop :=
  All model m state.ordinary ∧
  ∀ bounds ∈ state.intervals, Subtype (m bounds.1).1 (m bounds.2).1

structure Capture where
  lower : Nat
  center : Nat
  upper : Nat

def variables (capture : Nat → Capture) (m : Assignment) : Mode → Nat → Ty
  | .lower, name => (m (capture name).lower).1
  | .actual, name => (m (capture name).center).1
  | .upper, name => (m (capture name).upper).1

def Tracks (state : State) (capture : Nat → Capture) (exp : Expr) : Prop :=
  ∀ name ∈ reads exp,
    ((capture name).lower,(capture name).center) ∈ state.intervals ∧
    ((capture name).center,(capture name).upper) ∈ state.intervals

def InInterval (lo hi center : Ty) : Prop :=
  Subtype lo center ∧ Subtype center hi

/-- The center has the source meaning, not a value read from a solver slot.
The two bounds are the total where expression at the two polarities;
a nominal subexpression takes its actual arguments in both polarities. -/
def SourceWhere (catalogue : Constructors) (interp : GeneralNominalInspection.Interpretation)
    (capture : Nat → Capture) (m : Assignment) (pattern : Pattern) (exp : Expr) : Prop :=
  InInterval (value (variables capture m) .lower exp) (value (variables capture m) .upper exp)
    (eval (algebra catalogue interp) (variables capture m .actual) (normalize pattern))

theorem center_in_interval {state : State} {capture : Nat → Capture}
    {exp : Expr} (tracked : Tracks state capture exp) (m : Assignment) (valid : Models state m) :
    InInterval (value (variables capture m) .lower exp) (value (variables capture m) .upper exp)
      (value (variables capture m) .actual exp) := by
  apply interval
  intro name read
  exact ⟨valid.2 _ (tracked name read).1,valid.2 _ (tracked name read).2⟩

/-- Source normalization and total compilation give the same center. In any
model of the ordinary declarative state, the existing logical interval facts
for exactly the variance-sensitive reads are sufficient. -/
theorem source_where {state : State} {catalogue : Constructors} {interp}
    {capture : Nat → Capture} {pattern : Pattern} {exp : Expr}
    (compiled : translate catalogue interp pattern = some exp)
    (tracked : Tracks state capture exp) (m : Assignment) (valid : Models state m) :
    SourceWhere catalogue interp capture m pattern exp := by
  have extracted := center_in_interval tracked m valid
  have agreement : Equivalent (value (variables capture m) .actual exp)
      (eval (algebra catalogue interp) (variables capture m .actual) (normalize pattern)) :=
    GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized compiled
  exact ⟨subtype_trans extracted.1 agreement.1,subtype_trans agreement.2 extracted.2⟩

/-- An input-side certificate: it requires only successful source translation
and recorded ordinary intervals, not that a dictionary or its child is sound. -/
def WhereReady (state : State) (catalogue : Constructors) (interp : GeneralNominalInspection.Interpretation)
    (capture : Nat → Capture) (decl : Declaration) : Prop :=
  ∀ clause ∈ decl.requirements, ∀ pattern ∈ clause.arguments,
    ∃ exp, translate catalogue interp pattern = some exp ∧ Tracks state capture exp

theorem declaration_where {state : State} {catalogue : Constructors} {interp}
    {capture : Nat → Capture} {decl : Declaration}
    (ready : WhereReady state catalogue interp capture decl) (m : Assignment) (valid : Models state m) :
    ∀ clause ∈ decl.requirements, ∀ pattern ∈ clause.arguments,
      ∃ exp, translate catalogue interp pattern = some exp ∧
        SourceWhere catalogue interp capture m pattern exp := by
  intro clause present pat listed
  obtain ⟨exp,c,t⟩ := ready clause present pat listed
  exact ⟨exp,c,source_where c t m valid⟩


open CommonRoleOutermostResolver (All₂)

/-- Simultaneous transport for the actual ordered compiler result. Repeated
source patterns retain their positions; no quotient by membership is made. -/
theorem ordered_arguments {state : State} {catalogue : Constructors} {interp}
    {capture : Nat → Capture} (m : Assignment) (valid : Models state m)
    {patterns : List Pattern} {expressions : List Expr}
    (compiled : translateMany catalogue interp patterns = some expressions)
    (tracked : ∀ exp ∈ expressions, Tracks state capture exp) :
    All₂ (SourceWhere catalogue interp capture m) patterns expressions := by
  induction patterns generalizing expressions with
  | nil =>
    have eq : [] = expressions := Option.some.inj compiled
    subst expressions
    exact .nil
  | cons p ps ih =>
    unfold translateMany at compiled
    cases first : translate catalogue interp p with
    | none => simp [first] at compiled
    | some e =>
      cases rest : translateMany catalogue interp ps with
      | none => simp [first,rest] at compiled
      | some es =>
        have eq : e :: es = expressions := by simpa [first,rest] using compiled
        subst expressions
        exact .cons (source_where first (tracked e List.mem_cons_self) m valid)
          (ih rest (fun exp hit => tracked exp (List.mem_cons_of_mem _ hit)))

theorem ordered_clauses {state : State} {catalogue : Constructors} {interp}
    {capture : Nat → Capture} (m : Assignment) (valid : Models state m)
    {clauses : List Clause} {args : List (List Expr)}
    (compiled : All₂ (fun (clause : Clause) exps =>
      translateMany catalogue interp clause.arguments = some exps ∧
        ∀ exp ∈ exps, Tracks state capture exp) clauses args) :
    All₂ (fun (clause : Clause) exps =>
      All₂ (SourceWhere catalogue interp capture m) clause.arguments exps) clauses args := by
  induction compiled with
  | nil => exact .nil
  | cons one _ ih => exact .cons (ordered_arguments m valid one.1 one.2) ih

end Yulang.GeneralDeclarativeWhere319
