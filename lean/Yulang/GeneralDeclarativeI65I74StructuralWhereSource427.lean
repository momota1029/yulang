import Yulang.GeneralDeclarativeI65B6PairedTreeReplay400
import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeSubstitution320 (logical EquationRead equation_read)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany value)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeSourceEmission322 (exact_at useArg)
open CommonNominalFullCarrier (Equivalent)

def writtenRecord427 (label binder empty : Nat) : Pattern :=
  .record label (.var binder) (.app empty [])

def recordCode427 (label binder : Nat) : Expr :=
  .record label (.variable binder) (.primitive .emptyRecord [])

def translateWhere427 (s : State) : Pattern → Option Expr :=
  translate (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot)

def writtenRow427 {s q} (f : AuthoredBodyFrame393 s q) (name label binder : Nat) : Equation :=
  ⟨name,logical f.names.input .actual (recordCode427 label binder)⟩

/-- One original structural where argument before child classification.
The exact placed point is checked against a real ordinary equation
for literal source code and the actual lexical capture of that same
parent frame. Neither child success nor model equality is input. -/
structure OriginalRecordArgument427 {s q} (f : AuthoredBodyFrame393 s q)
    (clauseOrdinal argumentOrdinal : Nat) where
  clause : Clause
  atClause : f.decl.requirements[clauseOrdinal]? = some clause
  label : Nat
  binder : Nat
  empty : Nat
  written : clause.arguments[argumentOrdinal]? = some (writtenRecord427 label binder empty)
  inHead : binder ∈ f.decl.inputNames
  translation : translateWhere427 s (writtenRecord427 label binder empty) = some (recordCode427 label binder)
  name : Nat
  placed : f.placement.compound clause argumentOrdinal = point name
  rowOrdinal : Nat
  retained : s.current.ordinary.equations[rowOrdinal]? = some (writtenRow427 f name label binder)

def OriginalRecordArgument427.child {s q f k j}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k j) : Request :=
  ⟨q.occurrence ++ [k],(f.whereFor a.clause).demand⟩

theorem structural_where_keeps_original_child_at_ordinal427 {s q f k j}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k j) :
    (frameWhereKids400 f)[k]? = some a.child := by
  have hit : (f.clauses.map LiteralWhereEntry.demand)[k]? = some (f.whereFor a.clause).demand := by
    simp [AuthoredBodyFrame393.clauses,a.atClause]
  unfold frameWhereKids400 children OriginalRecordArgument427.child
  rw [List.getElem?_map,List.getElem?_zipIdx]
  simp [hit]

theorem structural_where_child_argument_is_placed_point427 {s q f k j}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k j) :
    a.child.demand.arguments[j]? = some (point a.name) := by
  have selected := exact_at f.names (f.placement.compound a.clause) 0 a.clause.arguments j a.written
  change (GeneralDeclarativeSourceEmission322.inputs f.names (f.placement.compound a.clause)
    0 a.clause.arguments)[j]? = _
  simpa only [Nat.zero_add,a.placed,useArg,writtenRecord427,normalize] using selected

theorem structural_where_point_denotes_original_compound_in_same_model427 {s q f k j}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k j) (m : Model) (fit : Fits s m) :
    Equivalent (m.assignment a.name).1
      (value (variables f.names.input m.assignment) .actual (recordCode427 a.label a.binder)) := by
  exact equation_read (.whole (List.mem_of_getElem? a.retained)) m.assignment fit.1.1

/-- The ordinal is a path coordinate, not a declaration/clause ID. -/
theorem different_original_clause_ordinals_have_different_child_occurrences427
    {s q f k j k' j'} (a : OriginalRecordArgument427 (s:=s) (q:=q) f k j)
    (b : OriginalRecordArgument427 (s:=s) (q:=q) f k' j') (h : k ≠ k') :
    a.child.occurrence ≠ b.child.occurrence := by
  intro collision
  change _ ++ [k] = _ ++ [k'] at collision
  simpa using h (List.cons.inj (List.append_cancel_left collision)).1

end Yulang.GeneralDeclarativeI65.StructuralWhere427
