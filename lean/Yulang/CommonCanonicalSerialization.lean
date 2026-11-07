import Yulang.CommonCanonicalCounterConstraints

/-!
# Ordinary finite-word serialization of the obstruction interfaces

All syntax constructors have fixed nonzero token digits. Natural fields are
unary terminated words. Lists carry cons/nil tags. Closed rows serialize their
actual finite lists of enabled coordinates, not their semantic predicates.
-/

namespace Yulang.CommonCanonicalSerialization

open CommonCanonicalRowSyntax
open CommonCanonicalRowTests

inductive Token where
  | natZero | natSucc | nil | cons
  | maskAll | maskOnly
  | rowParameter | rowClosed | rowEmpty | rowHead | rowUnion
  | rowProtect | rowRelease | rowResidual
  | typeUnit | typePair | typeUnion | typeArrow
  | interface
  | program | halt | increment | decrement | jump
  deriving DecidableEq, Repr

def Token.digit : Token → Nat
  | .natZero => 1 | .natSucc => 2 | .nil => 3 | .cons => 4
  | .maskAll => 5 | .maskOnly => 6
  | .rowParameter => 7 | .rowClosed => 8 | .rowEmpty => 9 | .rowHead => 10
  | .rowUnion => 11 | .rowProtect => 12 | .rowRelease => 13 | .rowResidual => 14
  | .typeUnit => 15 | .typePair => 16 | .typeUnion => 17 | .typeArrow => 18
  | .interface => 19 | .program => 20 | .halt => 21 | .increment => 22
  | .decrement => 23 | .jump => 24

def Token.fromDigit : Nat → Token
  | 1 => .natZero | 2 => .natSucc | 3 => .nil | 4 => .cons
  | 5 => .maskAll | 6 => .maskOnly
  | 7 => .rowParameter | 8 => .rowClosed | 9 => .rowEmpty | 10 => .rowHead
  | 11 => .rowUnion | 12 => .rowProtect | 13 => .rowRelease | 14 => .rowResidual
  | 15 => .typeUnit | 16 => .typePair | 17 => .typeUnion | 18 => .typeArrow
  | 19 => .interface | 20 => .program | 21 => .halt | 22 => .increment
  | 23 => .decrement | 24 => .jump
  | _ => .natZero

abbrev Word := List Token

def wordCode : Word → Nat
  | [] => 0
  | token :: rest => token.digit + 64 * wordCode rest

def natural : Nat → Word
  | 0 => [.natZero]
  | n + 1 => .natSucc :: natural n

def list (encode : α → Word) : List α → Word
  | [] => [.nil]
  | value :: rest => .cons :: (encode value ++ list encode rest)

def permission : CommonEffectRequestGeneration.Permission → Word
  | .all => [.maskAll]
  | .only keys => .maskOnly :: list natural keys

def row : Row scopes parameters → Word
  | .var (.inl index) => .rowParameter :: natural index.val
  | .var (.inr closed) => .rowClosed :: list (fun index => natural index.val) closed.enabled
  | .empty => [.rowEmpty]
  | .head key => .rowHead :: natural key
  | .union first last => .rowUnion :: (row first ++ row last)
  | .protect scope mask source => .rowProtect :: (natural scope.val ++ permission mask ++ row source)
  | .release scope mask source => .rowRelease :: (natural scope.val ++ permission mask ++ row source)
  | .residual handled source => .rowResidual :: (list natural handled ++ row source)

def form : Form scopes parameters → Word
  | .unit => [.typeUnit]
  | .pair first last => .typePair :: (form first ++ form last)
  | .union first last => .typeUnion :: (form first ++ form last)
  | .arrow input incoming output outgoing =>
      .typeArrow :: (form input ++ row incoming ++ form output ++ row outgoing)

def interface (value : Interface) : Word :=
  .interface :: (natural value.scopes ++ natural value.parameters ++ form value.value)

def interfaceCode (value : Interface) : Nat := wordCode (interface value)

def instruction : CanonicalRegisterMachine.Instruction registers states → Word
  | .halt => [.halt]
  | .increment register next => .increment :: (natural register.val ++ natural next.val)
  | .decrement register zero positive =>
      .decrement :: (natural register.val ++ natural zero.val ++ natural positive.val)
  | .goto next => .jump :: natural next.val

def program (value : CanonicalRegisterMachine.Program) : Word :=
  .program :: (natural value.registers ++ natural value.states ++ natural value.entry.val ++
    list instruction value.code)

def programCode (value : CanonicalRegisterMachine.Program) : Nat := wordCode (program value)

/-- Fixed-alphabet word coding has no representation collisions. -/
theorem wordCode_injective : Function.Injective wordCode := by
  have digitBounds (token : Token) : 0 < token.digit ∧ token.digit < 64 := by
    cases token <;> decide
  have roundtrip (token : Token) : Token.fromDigit token.digit = token := by
    cases token <;> rfl
  have digitInjective : Function.Injective Token.digit := by
    intro first last equal
    have recovered := congrArg Token.fromDigit equal
    simpa only [roundtrip] using recovered
  intro first
  induction first with
  | nil =>
      intro last equal
      cases last with
      | nil => rfl
      | cons token rest =>
          have bounds := digitBounds token
          simp only [wordCode] at equal
          omega
  | cons token rest ih =>
      intro last equal
      cases last with
      | nil =>
          have bounds := digitBounds token
          simp only [wordCode] at equal
          omega
      | cons other tail =>
          have firstBounds := digitBounds token
          have lastBounds := digitBounds other
          simp only [wordCode] at equal
          have same : token.digit = other.digit ∧ wordCode rest = wordCode tail := by omega
          exact congr (congrArg List.cons (digitInjective same.1)) (ih same.2)

/-- The closed fixed tuple has exactly the same concrete word when included
under a larger generalized row context. No bijection or equal arity premise
is used. -/
theorem form_rename_zero_serializes (value : Form scopes 0) (parameters : Nat) :
    form (value.rename (Fin.elim0 : Fin 0 → Fin parameters)) = form value := by
  have rows (value : Row scopes 0) :
      row (rowRename (Fin.elim0 : Fin 0 → Fin parameters) value) = row value := by
    induction value with
    | var index =>
        cases index with
        | inl index => exact Fin.elim0 index
        | inr closed => rfl
    | empty | head => rfl
    | union first last ihf ihl => simp only [rowRename, row, ihf, ihl]
    | protect scope mask source ih => simp only [rowRename, row, ih]
    | release scope mask source ih => simp only [rowRename, row, ih]
    | residual handled source ih => simp only [rowRename, row, ih]
  induction value with
  | unit => rfl
  | pair first last ihf ihl => simp only [Form.rename, form, ihf, ihl]
  | union first last ihf ihl => simp only [Form.rename, form, ihf, ihl]
  | arrow input incoming output outgoing ihi iho =>
      simp only [Form.rename, form, rows, ihi, iho]

def rowTypeWord (encodedRow : Word) : Word :=
  [.typeArrow, .typeUnit] ++ encodedRow ++ [.typeUnit, .rowEmpty]

def lockWord (encodedType : Word) : Word :=
  [.typeArrow] ++ encodedType ++ [.rowEmpty] ++ encodedType ++ [.rowEmpty]

def meetWord (first : Word) : List Word → Word
  | [] => rowTypeWord first
  | next :: rest => [.typeUnion] ++ rowTypeWord next ++ meetWord first rest

def fixedStream (tests : List (Test scopes parameters)) : Word :=
  tests.flatMap (fun test => [.typePair] ++ lockWord (rowTypeWord (row test.expected)))

def valueStream (tests : List (Test scopes parameters)) : Word :=
  tests.flatMap (fun test => [.typePair] ++ lockWord (meetWord (row test.first) (test.rest.map row)))

/-- The two tuple compilers are exactly finite streams of the displayed
templates. In particular, `meetForm` emits each rest-row first and the
distinguished first row last, preserving their original order. -/
theorem problem_stream_exact (tests : List (Test scopes parameters)) :
    form (problemFixed tests) = fixedStream tests ++ [.typeUnit] ∧
    form (problemValue tests) = valueStream tests ++ [.typeUnit] := by
  have meetExact (first : Row scopes parameters) (rest : List (Row scopes parameters)) :
      form (meetForm first rest) = meetWord (row first) (rest.map row) := by
    induction rest with
    | nil => rfl
    | cons next rest ih =>
        simp only [meetForm, form, rowForm, List.map_cons, meetWord, rowTypeWord,
          List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, ih]
  induction tests with
  | nil => exact ⟨rfl, rfl⟩
  | cons test tests ih =>
      constructor
      · simp only [problemFixed, form, Test.fixed, lockForm, rowForm, fixedStream,
          List.flatMap_cons, rowTypeWord, lockWord, List.singleton_append,
          List.cons_append, List.nil_append, List.append_assoc, ih.1]
      · simp only [problemValue, form, Test.value, lockForm, valueStream,
          List.flatMap_cons, lockWord, List.singleton_append, List.cons_append,
          List.nil_append, List.append_assoc, ih.2, meetExact]

end Yulang.CommonCanonicalSerialization
