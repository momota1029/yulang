import Yulang.GeneralDeclarativeI65I74MarkedBeforeCapture475

set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475.MarkedAudit
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeNestedSyntax332 (Node)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Occurrence)

def empty : Expr := .primitive .emptyRecord []
def outer : Equation := ⟨4,.record 30 (.variable 6) (.record 31 (.variable 90) empty)⟩
def inner : Equation := ⟨6,.record 40 (.variable 7) (.record 41 (.variable 91) empty)⟩
def unselectedLeft : Equation := ⟨90,.record 50 (.variable 90) empty⟩
def unselectedRight : Equation := ⟨91,.record 51 (.variable 91) empty⟩
def binderValue : Equation := ⟨7,.record 52 (.variable 7) empty⟩
def actualRows : List Equation := [outer,inner,unselectedLeft,unselectedRight,binderValue,outer,inner]
def originalAuthorRows : List Equation := [inner,outer,unselectedLeft,unselectedRight,binderValue,inner,outer]

def before : List StampedRead :=
  [⟨0,1,outer⟩,⟨1,0,inner⟩,⟨2,2,unselectedLeft⟩,⟨3,3,unselectedRight⟩,⟨4,4,binderValue⟩]
def later : List StampedRead :=
  [⟨5,6,outer⟩,⟨6,5,inner⟩,⟨2,2,unselectedLeft⟩,⟨3,3,unselectedRight⟩,⟨4,4,binderValue⟩]

def target : Node :=
  .record (.cons 30 (.record (.cons 40 (.capture 3) .nil) (.capture 73)) .nil) (.capture 74)

def positions {rows : List StampedRead} (answer : Option (Traced rows)) :
    Option (List (Nat × Nat × Nat)) :=
  answer.map fun read => read.opened.map fun e => (e.name,e.picked.raw,e.picked.author)

def someBinder {rows : List StampedRead} (answer : Option (Traced rows)) : Bool :=
  match answer.map Traced.uses with
  | some (⟨3,.actual,.variable 7⟩ :: _) => true
  | _ => false

def earlyRead := runMarked before .actual (.variable 4) target
def laterRead := runMarked later .actual (.variable 4) target

def actualTests : List Bool :=
  [valid actualRows originalAuthorRows before,valid actualRows originalAuthorRows later,
   positions earlyRead == some [(4,0,1),(6,1,0)],
   positions laterRead == some [(4,5,6),(6,6,5)],
   someBinder earlyRead,someBinder laterRead,
   positions (runMarked before .actual (.variable 7) (.capture 3)) == some [],
   (runMarked [⟨0,1,outer⟩] .actual (.variable 4) target).isSome]

theorem actual_marks_track_only_opened_names_and_do_not_pick_a_duplicate :
    actualTests = [true,true,true,true,true,true,true,false] := by decide +kernel

theorem both_runs_erase_to_the_same_exact_compiler_captures :
    earlyRead.map Traced.uses = laterRead.map Traced.uses := by rfl

/-- info: [true, true, true, true, true, true, true, false] -/
#guard_msgs in
#eval actualTests

#print axioms actual_marks_track_only_opened_names_and_do_not_pick_a_duplicate
#print axioms both_runs_erase_to_the_same_exact_compiler_captures
end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475.MarkedAudit
