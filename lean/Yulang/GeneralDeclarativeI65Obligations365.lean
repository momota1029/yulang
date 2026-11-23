import Yulang.GeneralDeclarativeI65Comparison365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals
  (Endpoint Bounds Argument Obligation ResultHolds decomposeArgument decomposeContextArgument
   decomposeContextArguments ContextObligation ContextWellFormed compileInContext
   result_some result_map_exact result_none append_exact childContext effectiveParameter valueChecks rowChecks)
open CommonDeclaredNominalInspection (Parameter Registry)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (compiled_full_exact)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

private def Need (s : GeneralDeclarativeHead320.State) (table : Registry) (context : Bool) :
    Obligation Nat → Prop
  | .value a b => Nonempty (Compare s table context a b)
  | .row a b => Atom.rowLe a b ∈ s.normal.ordinary

private theorem argument_of_needs {s : GeneralDeclarativeHead320.State} {table : Registry} {context : Bool}
    (p : Parameter) (a b : Argument Nat)
    (facts : ResultHolds (Need s table context) (decomposeArgument p a b)) :
    Nonempty (CompareArgument s table context p a b) := by
  rcases p with ⟨kind,mode⟩
  cases kind <;> cases mode <;> cases a <;> cases b
  all_goals rename_i l r
  all_goals cases l <;> cases r
  all_goals simp [decomposeArgument,Need,valueChecks,rowChecks,Bounds.checks,Bounds.lower,Bounds.upper] at facts
  all_goals solve
    | exact ⟨.unusedValue _ _⟩
    | exact ⟨.unusedRow _ _⟩
    | obtain ⟨read⟩ := facts; exact ⟨.covariantValue read⟩
    | obtain ⟨read⟩ := facts; exact ⟨.contravariantValue read⟩
    | obtain ⟨⟨a⟩,⟨b⟩,⟨c⟩,⟨d⟩⟩ := facts; exact ⟨.invariantValue a d b c⟩
    | exact ⟨.covariantRow facts⟩
    | exact ⟨.contravariantRow facts⟩
    | exact ⟨.invariantRow facts.1 facts.2.2.2 facts.2.1 facts.2.2.1⟩

def ContextNeed (s : GeneralDeclarativeHead320.State) (table : Registry) (p : ContextObligation Nat) : Prop :=
  Need s table p.1 p.2

theorem context_arguments_of_needs {s : GeneralDeclarativeHead320.State} {table : Registry} {ctx : Bool}
    (decl : List Parameter) (first last : List (Argument Nat))
    (proved : ResultHolds (ContextNeed s table) (decomposeContextArguments ctx decl first last)) :
    Nonempty (CompareArguments s table ctx decl first last) := by
  induction decl generalizing first last with
  | nil =>
    cases first <;> cases last
    · exact ⟨.nil⟩
    all_goals exact False.elim (result_none _ proved)
  | cons p ps ih =>
    cases first with
    | nil => exact False.elim (result_none _ proved)
    | cons a as =>
      cases last with
      | nil => exact False.elim (result_none _ proved)
      | cons b bs =>
        rw [decomposeContextArguments,append_exact] at proved
        have head : ResultHolds (Need s table (childContext ctx p))
            (decomposeArgument (effectiveParameter ctx p) a b) := by
          have sh := proved.1
          rw [decomposeContextArgument,result_map_exact] at sh
          exact sh
        obtain ⟨h⟩ := argument_of_needs (effectiveParameter ctx p) a b head
        obtain ⟨t⟩ := ih as bs proved.2
        exact ⟨.cons h t⟩

end Yulang.GeneralDeclarativeI65
