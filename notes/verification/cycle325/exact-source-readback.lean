import Yulang.GeneralDeclarativeAdvanceFixture325
import Yulang.GeneralDeclarativeNamedAliasResolve325
import Yulang.GeneralDeclarativeCompoundResolve325
import Yulang.GeneralDeclarativeFreshInputs325
import Yulang.GeneralDeclarativeReplayFixture325
import Yulang.GeneralDeclarativePlacedClause325

open Yulang
open GeneralDeclarativeCompoundDecl325 (inner outer innerCode outerCode)
open GeneralDeclarativeSparseWhere325 (plan atPosition bodies)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)

example : GeneralDeclarativeCompoundDecl325.call.arguments = [⟨8,9,10⟩] := rfl
example : ¬ ∃ e, (⟨1,e⟩ : GeneralDeclarativeHead320.Equation) ∈
    GeneralDeclarativeCompoundState325.final.equations :=
  GeneralDeclarativeCompoundState325.absence_of_center_row

abbrev mixedPatterns : List Pattern := [.var 0, inner, .var 0, outer]
abbrev mixed := plan mixedPatterns [.variable 0,innerCode,.variable 0,outerCode]
example : mixed = [none,some innerCode,none,some outerCode] := rfl
example : atPosition 70 mixed 1 = ⟨70,71,72⟩ := rfl
example : atPosition 70 mixed 3 = ⟨73,74,75⟩ := rfl
example (cap : Nat → Capture) : (bodies cap mixed).length = 6 := rfl

#check @GeneralDeclarativeFrameReadback325.complete_read
#check @GeneralDeclarativeSourceSelection325.actual_local_compiler
#check @GeneralDeclarativeSourceSelection325.sound
#check @GeneralDeclarativeSourceFixture325.early_frame_but_unrecorded
#check @GeneralDeclarativeAdvanceFixture325.composed_actual
#check @GeneralDeclarativeNamedAliasResolve325.real_nonliteral
#check @GeneralDeclarativeCompoundResolve325.genuine_compound
#check @GeneralDeclarativeFreshInputs325.whole_input_projection
#check @GeneralDeclarativeReplayFixture325.fixed_root_read
#check @GeneralDeclarativeReplayFixture325.source_compiles_after
#check @GeneralDeclarativePlacedClause325.bound_to_producing_clause

section FreshFixedTarget
open GeneralDeclarativeCompoundDecl325 (clause impl interpret impl_checked)
open GeneralDeclarativeCompoundState325 (initial)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeFreshInputs325 (prepared whole_input_projection names_bounded)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Models)

abbrev protectedTargets : List Nat := [5,6]
abbrev compoundJobs := plan clause.arguments [innerCode]
abbrev compoundCap (_ : Nat) := point 3
abbrev freshTriple := atPosition (seed initial protectedTargets compoundCap compoundJobs) compoundJobs 0
abbrev extended := prepared initial protectedTargets compoundCap compoundJobs

example : freshTriple = ⟨11,12,13⟩ := rfl

theorem fresh_clause_keeps_fixed_targets (m) (valid : Models initial m) :
    Bounds extended freshTriple ∧ ∃ new, Models extended new ∧ new 5 = m 5 ∧ new 6 = m 6 := by
  have declares : clause ∈ impl.requirements := List.mem_cons_self
  have spelled : GeneralNominalCenteredHeadMatExpressions.translateMany constructors interpret
      (clause.arguments.map GeneralDeclarationPatterns.normalize) = some [innerCode] := rfl
  have span : ∀ n ∈ impl.inputNames, Bounds initial (compoundCap n) := fun _ _ => ⟨.refl _,.refl _⟩
  obtain ⟨new,got,keep⟩ := (whole_input_projection impl_checked declares spelled span protectedTargets m).mp valid
  exact ⟨names_bounded (show compoundJobs[0]? = some (some innerCode) from rfl),new,got,
    keep 5 (List.mem_append_right _ List.mem_cons_self),
    keep 6 (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

#print axioms fresh_clause_keeps_fixed_targets
end FreshFixedTarget
