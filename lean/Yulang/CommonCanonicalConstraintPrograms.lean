import Yulang.CommonCanonicalGridPrograms

/-! Concrete finite scripts for the existing counter-to-row constraint compiler. -/

namespace Yulang.CommonCanonicalConstraintPrograms

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalWordPrograms
open CommonCanonicalRangeEmitters
open CommonCanonicalTemplatePrograms
open CommonCanonicalGridPrograms
open CommonCanonicalRowSyntax
open CommonCanonicalRowTests
open CommonCanonicalCounterConstraints

inductive Mode where
  | fixed | value

def stream (mode : Mode) (tests : List (Test scopes parameters)) : Word :=
  match mode with
  | .fixed => fixedStream tests
  | .value => valueStream tests

def literal (tokens : Word) : Script parameters := .atom (.literal tokens)
local infixr:65 " <+> " => Script.append

def rowType (source : Script parameters) : Script parameters :=
  literal [.typeArrow, .typeUnit] <+> source <+> literal [.typeUnit, .rowEmpty]

def lock (source : Script parameters) : Script parameters :=
  literal [.typeArrow] <+> source <+> literal [.rowEmpty] <+> source <+> literal [.rowEmpty]

def meet (first : Script parameters) : List (Script parameters) → Script parameters
  | [] => rowType first
  | next :: rest => literal [.typeUnion] <+> rowType next <+> meet first rest

def testScript (mode : Mode) (first : Script parameters) (rest : List (Script parameters))
    (expected : Script parameters) : Script parameters :=
  literal [.typePair] <+> lock (match mode with
    | .fixed => rowType expected
    | .value => meet first rest)

/-- The template follows the precise lock and meet syntax of the original
constraint compiler, including the order of all rows in a meet. -/
theorem testScript_tokens (mode : Mode) (first : Script parameters) (rest : List (Script parameters))
    (expected : Script parameters) (environment : Environment parameters) :
    (testScript mode first rest expected).tokens environment =
      [.typePair] ++ lockWord (match mode with
        | .fixed => rowTypeWord (expected.tokens environment)
        | .value => meetWord (first.tokens environment) (rest.map (fun script => script.tokens environment))) := by
  have meetExact : (meet first rest).tokens environment =
      meetWord (first.tokens environment) (rest.map (fun script => script.tokens environment)) := by
    induction rest with
    | nil => simp only [meet, rowType, Script.tokens, literal, Template.tokens, meetWord,
        rowTypeWord, List.map_nil, List.append_assoc]
    | cons next rest ih => simp only [meet, rowType, Script.tokens, literal, Template.tokens, meetWord,
        rowTypeWord, List.map_cons, List.append_assoc, ih]
  cases mode <;> simp only [testScript, Script.tokens, literal, Template.tokens, lock,
    rowType, rowTypeWord, lockWord, meetExact, List.append_assoc]

-- The readonly roster also includes cursor 0 and scan fuel 9, although
-- neither is used as a field of the emitted constraint syntax.
abbrev inputField : Fin 10 := 1
abbrev registersField : Fin 10 := 2
abbrev statesField : Fin 10 := 3
abbrev entryField : Fin 10 := 4
abbrev operandFirst : Fin 10 := 5
abbrev operandSecond : Fin 10 := 6
abbrev operandThird : Fin 10 := 7
abbrev pcField : Fin 10 := 8

def emptyRowScript : Script 10 := literal [.rowEmpty]

def gridScript (excluded : Option (Fin 10)) : Script 10 :=
  literal [.rowClosed] <+> .grid registersField excluded

def reachScript : Script 10 :=
  literal [.rowParameter] <+> .atom (.number pcField)

def complementScript (source : Fin 10) : Script 10 :=
  literal [.rowParameter] <+> .atom (.sum statesField source)

def protectScript (source : Fin 10) (body : Script 10) : Script 10 :=
  literal [.rowProtect] <+> .atom (.number source) <+> literal [.maskOnly, .nil] <+> body

def releaseScript (source : Fin 10) (body : Script 10) : Script 10 :=
  literal [.rowRelease] <+> .atom (.number source) <+> literal [.maskOnly, .nil] <+> body

def seedScript : Script 10 :=
  .atom (.copies inputField [.rowProtect, .natZero, .maskOnly, .nil]) <+> literal [.rowHead, .natZero]

def seedTestScript (mode : Mode) : Script 10 :=
  testScript mode seedScript [complementScript entryField] emptyRowScript

/-- The runtime seed repetition emits exactly the finite seed of the
counter-to-row compiler, for every numeric input. -/
theorem seed_script_exact (source : Program) (input : Nat) (mode : Mode) (environment : Environment 10)
    (inputEq : environment inputField = input) (statesEq : environment statesField = source.states)
    (entryEq : environment entryField = source.entry.val) :
    (seedTestScript mode).tokens environment =
      stream mode [forbidden (seed source.registers input) [complementRow source.entry]] := by
  have seedWord (n : Nat) : row (seed source.registers n : Row (source.registers + 1) (source.states + source.states)) =
      repeatTokens [.rowProtect, .natZero, .maskOnly, .nil] n ++ [.rowHead, .natZero] := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [seed, row, Fin.val_zero, natural, permission, list, repeatTokens, ih,
        List.cons_append, List.nil_append]
  rw [seedTestScript, testScript_tokens]
  cases mode <;> simp only [stream, fixedStream, valueStream, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, forbidden, emptyRowScript, seedScript, complementScript,
    Script.tokens, literal, Template.tokens, row, complementRow, seedWord, inputEq, statesEq, entryEq,
    Fin.val_natAdd, List.map_cons, List.map_nil, List.singleton_append]

def partitionScript (mode : Mode) : Script 10 :=
  testScript mode (literal [.rowUnion] <+> reachScript <+> complementScript pcField) [] (gridScript none) <+>
    testScript mode reachScript [complementScript pcField] emptyRowScript

theorem partition_script_exact {states : Nat} (registers : Nat) (pc : Fin states) (mode : Mode)
    (environment : Environment 10) (registersEq : environment registersField = registers)
    (statesEq : environment statesField = states) (pcEq : environment pcField = pc.val) :
    (partitionScript mode).tokens environment = stream mode (partitionTests registers pc) := by
  have gridExact := (grid_serialization_exact (registers + 1) 0).1
  simp only [partitionScript, Script.tokens, testScript_tokens]
  cases mode <;> simp only [stream, partitionTests, fixedStream, valueStream, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, forbidden, emptyRowScript, gridScript, reachScript, complementScript,
    Script.tokens, literal, Template.tokens, gridExact, row, reachRow, complementRow,
    registersEq, statesEq, pcEq, Fin.val_castAdd, Fin.val_natAdd, List.map_cons, List.map_nil,
    List.singleton_append] <;> rfl

inductive Kind where
  | halt | increment | decrement | jump

def kind {registers states : Nat} : Instruction registers states → Kind
  | .halt => .halt
  | .increment _ _ => .increment
  | .decrement _ _ _ => .decrement
  | .goto _ => .jump

def operandValues {registers states : Nat} (environment : Environment 10) : Instruction registers states → Prop
  | .halt => True
  | .increment register next => environment operandFirst = register.val ∧ environment operandSecond = next.val
  | .decrement register zero positive => environment operandFirst = register.val ∧
      environment operandSecond = zero.val ∧ environment operandThird = positive.val
  | .goto next => environment operandFirst = next.val

def instructionScript (mode : Mode) : Kind → Script 10
  | .halt => testScript mode reachScript [] emptyRowScript
  | .increment => testScript mode (protectScript operandFirst reachScript)
      [complementScript operandSecond] emptyRowScript
  | .decrement =>
      testScript mode reachScript [gridScript (some operandFirst), complementScript operandSecond] emptyRowScript <+>
      testScript mode (releaseScript operandFirst reachScript)
        [releaseScript operandFirst (protectScript operandFirst (gridScript none)), complementScript operandThird]
        emptyRowScript
  | .jump => testScript mode reachScript [complementScript operandFirst] emptyRowScript

/-- Every instruction handler emits exactly its original constraint stream.
The decrement case keeps the literal release(protect(grid)) expression. -/
theorem instruction_script_exact {registers states : Nat} (pc : Fin states)
    (instruction : Instruction registers states) (mode : Mode) (environment : Environment 10)
    (registersEq : environment registersField = registers) (statesEq : environment statesField = states)
    (pcEq : environment pcField = pc.val) (operands : operandValues environment instruction) :
    (instructionScript mode (kind instruction)).tokens environment = stream mode (instructionTests pc instruction) := by
  have gridExact := (grid_serialization_exact (registers + 1) (states + states)).1
  have zeroExact := (grid_serialization_exact (registers + 1) (states + states)).2
  cases instruction <;> cases mode <;>
    simp_all only [kind, operandValues, instructionScript, Script.tokens, testScript_tokens,
      stream, instructionTests, fixedStream, valueStream, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, forbidden, emptyRowScript, gridScript, reachScript, complementScript,
      protectScript, releaseScript, Script.tokens, literal, Template.tokens,
      positiveRow, row, permission, list, reachRow, complementRow, Fin.val_castAdd, Fin.val_natAdd,
      List.map_cons, List.map_nil, List.singleton_append, List.append_assoc]
  unfold gridEntry
  simp_all only []

end Yulang.CommonCanonicalConstraintPrograms
