import Yulang.CommonCanonicalScanPrograms
import Yulang.CanonicalRegisterGuard

namespace Yulang.CommonCanonicalReductionMachine

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalTemplatePrograms
open CommonCanonicalGridPrograms
open CommonCanonicalConstraintPrograms
open CommonCanonicalCounterConstraints
open CommonCanonicalRowTests
open CommonCanonicalProgramReader
open CommonCanonicalWordReverse

def tupleBody (mode : Mode) : Routine 16 :=
  append ((seedTestScript mode).compile context)
    (append (scanAll mode) ((literal [Token.typeUnit] : Script 10).compile context))

/-- The full finite constraint tuple, terminated by unit, is emitted by an
actual seed/scan sequence for either side of the reduction. -/
theorem tupleBody_runs (source : Program) (input : Nat) (mode : Mode) (values : Values) (prior : Word)
    (cursor : values 0 = wordCode (list instruction source.code)) (encoded : values 1 = wordCode prior)
    (inputEq : environment values inputField = input)
    (registersEq : environment values registersField = source.registers)
    (statesEq : environment values statesField = source.states)
    (entryEq : environment values entryField = source.entry.val) :
    ∃ finalValues, Runs (tupleBody mode) values finalValues ∧
      finalValues 1 = wordCode ((stream mode (constraints source input) ++ [Token.typeUnit]).reverse ++ prior) ∧
      ∀ field, HeaderField field → environment finalValues field = environment values field := by
  obtain ⟨seeded, seedRun, seedWord, seedFrame⟩ := script_emits context (seedTestScript mode) values prior encoded
  change seeded 1 = wordCode (((seedTestScript mode).tokens (environment values)).reverse ++ prior) at seedWord
  rw [seed_script_exact source input mode (environment values) inputEq statesEq entryEq] at seedWord
  obtain ⟨scanned, scanRun, scanWord, scanFrame⟩ := scanAll_runs source mode seeded _
    ((seedFrame 0).trans cursor) seedWord ((seedFrame registersField).trans registersEq)
    ((seedFrame statesField).trans statesEq)
  obtain ⟨finalValues, finishRun, finalWord, finishFrame⟩ :=
    script_emits context (literal [Token.typeUnit] : Script 10) scanned _ scanWord
  change finalValues 1 = _ at finalWord
  have whole : stream mode (constraints source input) =
      stream mode [forbidden (seed source.registers input) [complementRow source.entry]] ++
      stream mode ((List.finRange source.states).flatMap (fun pc =>
        partitionTests source.registers pc ++ instructionTests pc (instructionAt source pc))) := by
    cases mode <;> simp only [constraints, stream, fixedStream, valueStream, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  refine ⟨finalValues, append_runs seedRun (append_runs scanRun finishRun), ?_, ?_⟩
  · simpa only [whole, Script.tokens, literal, Template.tokens, List.reverse_append, List.append_assoc] using finalWord
  · intro field kept
    exact (finishFrame field).trans ((scanFrame field kept).trans (seedFrame field))

def headerRegisters (index : Fin 3) : Register := ⟨index.val + 7, by omega⟩

def Loaded (source : Program) (values : Values) : Prop :=
  values 0 = wordCode (list instruction source.code) ∧
  environment values inputField = programCode source ∧
  environment values registersField = source.registers ∧
  environment values statesField = source.states ∧
  environment values entryField = source.entry.val

def reload : Routine 16 := append (copy 6 0 5) (readHeader readerBank headerRegisters)

/-- Load the original saved program afresh while retaining the accumulated
interface word; this is used between the fixed and varying tuple passes. -/
theorem reload_runs (source : Program) (values : Values) (saved : values 6 = programCode source) :
    ∃ finalValues, Runs reload values finalValues ∧ Loaded source finalValues ∧ finalValues 1 = values 1 := by
  let entered := write (write values 0 (values 6)) 5 0
  have copying := copy_runs (6 : Register) 0 5 (by decide) (by decide) (by decide) values
  have readerDistinct : Function.Injective readerBank :=
    fourBank_injective 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have outside (field : Fin 3) (index : Fin 4) : headerRegisters field ≠ readerBank index := by
    have bound : (readerBank index).val ≤ 4 := by
      have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases alternatives with rfl | rfl | rfl | rfl <;> decide
    apply Fin.ne_of_val_ne
    change field.val + 7 ≠ (readerBank index).val
    omega
  have parsed := readHeader_runs readerBank readerDistinct headerRegisters outside source entered saved
  refine ⟨_, append_runs copying parsed, ?_, rfl⟩
  exact ⟨rfl, saved, rfl, rfl, rfl⟩

def headerScript (family : Bool) : Script 10 :=
  .append (literal [.interface, .natSucc])
    (.append (.atom (.number registersField))
      (if family then .append (.atom (.sum statesField statesField)) (literal [.typeUnion])
       else literal [.natZero]))

def headerTokens (family : Bool) (registers states : Nat) : Word :=
  [.interface] ++ natural (registers + 1) ++ natural (if family then states + states else 0) ++
    (if family then [.typeUnion] else [])

def startBuilder (family : Bool) : Routine 16 :=
  append (copy 0 6 5) (append (clear 1) (append reload ((headerScript family).compile context)))

theorem startBuilder_runs (source : Program) (family : Bool) (values : Values)
    (encoded : values 0 = programCode source) :
    ∃ finalValues, Runs (startBuilder family) values finalValues ∧ Loaded source finalValues ∧
      finalValues 1 = wordCode ((headerTokens family source.registers source.states).reverse) := by
  let saved := write (write values 6 (values 0)) 5 0
  let emptied := write saved 1 0
  have copying := copy_runs (0 : Register) 6 5 (by decide) (by decide) (by decide) values
  have clearing := clear_runs (1 : Register) saved
  obtain ⟨loaded, loading, loadedFields, outputSame⟩ := reload_runs source emptied encoded
  obtain ⟨cursor, inputEq, registersEq, statesEq, entryEq⟩ := loadedFields
  have emptyOutput : loaded 1 = wordCode [] := outputSame
  obtain ⟨finalValues, emitting, result, frame⟩ := script_emits context (headerScript family) loaded [] emptyOutput
  change finalValues 1 = wordCode (((headerScript family).tokens (environment loaded)).reverse ++ []) at result
  have tokens : (headerScript family).tokens (environment loaded) = headerTokens family source.registers source.states := by
    cases family <;> simp only [headerScript, Script.tokens, literal, Template.tokens, headerTokens,
      Bool.false_eq_true, ↓reduceIte, registersEq, statesEq, natural,
      List.cons_append, List.nil_append, List.append_nil, List.append_assoc]
  rw [tokens, List.append_nil] at result
  refine ⟨finalValues, append_runs copying (append_runs clearing (append_runs loading emitting)), ?_, result⟩
  exact ⟨(frame 0).trans cursor, (frame inputField).trans inputEq,
    (frame registersField).trans registersEq, (frame statesField).trans statesEq, (frame entryField).trans entryEq⟩

def targetInterface (family : Bool) (source : Program) : CommonCanonicalRowSyntax.Interface :=
  if family then familyInterface (constraints source (programCode source))
  else fixedInterface (constraints source (programCode source))

def reversedBuilder (family : Bool) : Routine 16 :=
  append (startBuilder family)
    (if family then append (tupleBody .fixed) (append reload (tupleBody .value)) else tupleBody .fixed)

/-- Both complete passes produce the exact existing interface serialization
in the reverse accumulator. No semantic row predicate is serialized. -/
theorem reversedBuilder_runs (source : Program) (family : Bool) (values : Values)
    (encoded : values 0 = programCode source) :
    ∃ finalValues, Runs (reversedBuilder family) values finalValues ∧
      finalValues 1 = wordCode ((interface (targetInterface family source)).reverse) := by
  obtain ⟨ready, starting, loaded, headerWord⟩ := startBuilder_runs source family values encoded
  obtain ⟨cursor, inputEq, registersEq, statesEq, entryEq⟩ := loaded
  obtain ⟨fixed, fixedRun, fixedWordEq, fixedFrame⟩ := tupleBody_runs source (programCode source) .fixed ready _
    cursor headerWord inputEq registersEq statesEq entryEq
  cases family with
  | false =>
      refine ⟨fixed, append_runs starting fixedRun, ?_⟩
      change fixed 1 = wordCode ((interface (fixedInterface (constraints source (programCode source)))).reverse)
      rw [(interfaces_stream_exact (constraints source (programCode source))).1]
      simpa only [fixedWord, stream, headerTokens, Bool.false_eq_true, ↓reduceIte, natural,
        List.reverse_append, List.append_nil, List.append_assoc] using fixedWordEq
  | true =>
      have saved : fixed 6 = programCode source :=
        (fixedFrame inputField (by unfold HeaderField; decide)).trans inputEq
      obtain ⟨loadedAgain, reloading, loadedFields, outputSame⟩ := reload_runs source fixed saved
      obtain ⟨secondCursor, secondInput, secondRegisters, secondStates, secondEntry⟩ := loadedFields
      obtain ⟨finalValues, valueRun, finalWord, _⟩ := tupleBody_runs source (programCode source) .value loadedAgain _
        secondCursor (outputSame.trans fixedWordEq) secondInput secondRegisters secondStates secondEntry
      refine ⟨finalValues, append_runs starting (append_runs fixedRun (append_runs reloading valueRun)), ?_⟩
      change finalValues 1 = wordCode ((interface (familyInterface (constraints source (programCode source)))).reverse)
      rw [(interfaces_stream_exact (constraints source (programCode source))).2]
      simpa only [familyWord, stream, headerTokens, ↓reduceIte, natural,
        List.reverse_append, List.append_assoc] using finalWord

def reverseBank : WordBank 16 := fourBank 1 2 3 4

def builderRoutine (family : Bool) : Routine 16 :=
  append (reversedBuilder family) (reverseWord reverseBank 0)

/-- The complete concrete routine returns the ordinary, forward serialized
interface code in the counter machine's designated output register zero. -/
theorem builderRoutine_runs (source : Program) (family : Bool) (values : Values)
    (encoded : values 0 = programCode source) :
    ∃ finalValues, Runs (builderRoutine family) values finalValues ∧
      finalValues 0 = interfaceCode (targetInterface family source) := by
  obtain ⟨reversed, building, reversedWord⟩ := reversedBuilder_runs source family values encoded
  have distinct : Function.Injective reverseBank :=
    fourBank_injective 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have outside (index : Fin 4) : (0 : Register) ≠ reverseBank index := by
    have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases alternatives with rfl | rfl | rfl | rfl <;> decide
  have reversal := reverseWord_runs reverseBank distinct 0 outside
    ((interface (targetInterface family source)).reverse) reversed reversedWord
  refine ⟨_, append_runs building reversal, ?_⟩
  change wordCode ((interface (targetInterface family source)).reverse.reverse) =
    interfaceCode (targetInterface family source)
  rw [List.reverse_reverse]
  rfl

def builder (family : Bool) : Program := (builderRoutine family).compile

/-- Two fixed finite programs realize the complete semantic reduction on
ordinary serialized source programs and ordinary serialized interfaces. -/
theorem builder_program_runs (source : Program) (family : Bool) :
    CanonicalRegisterMachine.Runs (builder family) (programCode source)
      (interfaceCode (targetInterface family source)) := by
  obtain ⟨finalValues, execution, output⟩ := builderRoutine_runs source family
    (initial (builder family) (programCode source)).values rfl
  have compiled := CanonicalRegisterGuard.routine_program_runs (routine := builderRoutine family)
    (programCode source) execution
  rw [output] at compiled
  exact compiled

end Yulang.CommonCanonicalReductionMachine
