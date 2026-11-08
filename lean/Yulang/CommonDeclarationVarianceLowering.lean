import Yulang.CommonDeclarationVarianceOccurrences
import Yulang.CommonNominalFieldTemplates
import Yulang.CommonDeclaredNominalInspection

/-!
# Lowering original resolved field bodies for variance

The input is the existing `CommonNominalFieldTemplates.Body`, with its exact
local node and type/row parameter references. The resolver returns original
formal identities and kinds, never variances. Every nominal application is
checked for lookup, arity and kind before lowering, including arguments that
will later prove unused. Arrow inputs and incoming rows are negative; results
and outgoing rows are positive. The whole arrow lies behind one wrapper
barrier. All alternatives, record tails and explicit default sources remain.

`Lowered` and `ArgumentsLowered` are structural source judgments, independent
of the executable option-valued compiler. Their iff theorems expose exactly
which original declarations enter the finite occurrence calculation.
-/

namespace Yulang.CommonDeclarationVarianceLowering

open CommonDeclarationVarianceSyntax
open CommonNominalFieldTemplates (Body TemplateRow)
open CommonDeclaredNominalInspection (Kind)

variable {Index Parameter : Type}

structure Scope (Index Parameter : Type) (nodes types rows : Nat) where
  node : Fin nodes → Index
  type : Fin types → Parameter
  row : Fin rows → Parameter

abbrev Header (Parameter : Type) := List (Kind × Parameter)
abbrev Resolver (Parameter : Type) := Nat → Option (Header Parameter)
abbrev Argument (nodes types rows : Nat) := (Fin nodes ⊕ Fin types) ⊕ TemplateRow rows

def reference (scope : Scope Index Parameter nodes types rows) :
    Fin nodes ⊕ Fin types → Expr Index Parameter
  | .inl index => .reference (scope.node index)
  | .inr parameter => .parameter (scope.type parameter)

def row (scope : Scope Index Parameter nodes types rows) : TemplateRow rows → Expr Index Parameter
  | .var parameter => .parameter (scope.row parameter)
  | .empty | .heads _ => .empty
  | .join first last => .both (row scope first) (row scope last)

def argumentKind : Argument nodes types rows → Kind
  | .inl _ => .value
  | .inr _ => .row

def argument (scope : Scope Index Parameter nodes types rows) :
    Argument nodes types rows → Expr Index Parameter
  | .inl source => reference scope source
  | .inr source => row scope source

def lowerArguments (scope : Scope Index Parameter nodes types rows) :
    Header Parameter → List (Argument nodes types rows) → Option (Expr Index Parameter)
  | [], [] => some .empty
  | (kind, formal) :: formals, actual :: actuals =>
      if kind = argumentKind actual then
        (lowerArguments scope formals actuals).map fun rest =>
          .both (.application formal (argument scope actual)) rest
      else none
  | _, _ => none

def ArgumentsLowered (scope : Scope Index Parameter nodes types rows) :
    Header Parameter → List (Argument nodes types rows) → Expr Index Parameter → Prop
  | [], [], result => result = .empty
  | (kind, formal) :: formals, actual :: actuals, result =>
      kind = argumentKind actual ∧ ∃ rest,
        ArgumentsLowered scope formals actuals rest ∧
        result = .both (.application formal (argument scope actual)) rest
  | _, _, _ => False

theorem lower_arguments_exact (scope : Scope Index Parameter nodes types rows)
    (formals : Header Parameter) (actuals : List (Argument nodes types rows))
    (result : Expr Index Parameter) :
    lowerArguments scope formals actuals = some result ↔ ArgumentsLowered scope formals actuals result := by
  induction formals generalizing actuals result with
  | nil => cases actuals <;> simp [lowerArguments, ArgumentsLowered, eq_comm]
  | cons formal formals ih =>
      obtain ⟨kind, parameter⟩ := formal
      cases actuals with
      | nil => simp [lowerArguments, ArgumentsLowered]
      | cons actual actuals =>
          by_cases valid : kind = argumentKind actual
          · simp only [lowerArguments, valid, ↓reduceIte, ArgumentsLowered, true_and]
            rw [Option.map_eq_some_iff]
            constructor
            · rintro ⟨rest, compiled, rfl⟩
              exact ⟨rest, (ih _ _).mp compiled, rfl⟩
            · rintro ⟨rest, lowered, rfl⟩
              exact ⟨rest, (ih _ _).mpr lowered, rfl⟩
          · simp [lowerArguments, ArgumentsLowered, valid]

def combine (first last : Option (Expr Index Parameter)) : Option (Expr Index Parameter) :=
  first.bind fun left => last.map fun right => .both left right

private theorem combine_exact (first last : Option (Expr Index Parameter)) (result) :
    combine first last = some result ↔
      ∃ left right, first = some left ∧ last = some right ∧ result = .both left right := by
  cases first <;> cases last <;> simp [combine, eq_comm]

def arrow (scope : Scope Index Parameter nodes types rows)
    (input : Fin nodes ⊕ Fin types) (incoming : TemplateRow rows)
    (output : Fin nodes ⊕ Fin types) (outgoing : TemplateRow rows) : Expr Index Parameter :=
  .barrier (.both (.negative (reference scope input))
    (.both (.negative (row scope incoming)) (.both (reference scope output) (row scope outgoing))))

def lower (scope : Scope Index Parameter nodes types rows) (resolve : Resolver Parameter) :
    Body nodes types rows → Option (Expr Index Parameter)
  | .parameter parameter => some (.parameter (scope.type parameter))
  | .base _ | .float | .bottom | .top | .emptyRecord | .exactEmpty => some .empty
  | .union first last | .inter first last => combine (lower scope resolve first) (lower scope resolve last)
  | .pair first last => some (.both (reference scope first) (reference scope last))
  | .record _ payload rest => (lower scope resolve rest).map (.both (reference scope payload))
  | .recordDefault _ source fallback => (lower scope resolve source).map (fun first => .both first (reference scope fallback))
  | .variant _ payload => some (reference scope payload)
  | .arrow input incoming output outgoing => some (arrow scope input incoming output outgoing)
  | .mask _ source => lower scope resolve source
  | .nominal name actuals => (resolve name).bind fun formals => lowerArguments scope formals actuals

def Lowered (scope : Scope Index Parameter nodes types rows) (resolve : Resolver Parameter) :
    Body nodes types rows → Expr Index Parameter → Prop
  | .parameter parameter, result => result = .parameter (scope.type parameter)
  | .base _, result | .float, result | .bottom, result | .top, result |
      .emptyRecord, result | .exactEmpty, result => result = .empty
  | .union first last, result | .inter first last, result =>
      ∃ left right, Lowered scope resolve first left ∧ Lowered scope resolve last right ∧ result = .both left right
  | .pair first last, result => result = .both (reference scope first) (reference scope last)
  | .record _ payload rest, result => ∃ tail, Lowered scope resolve rest tail ∧ result = .both (reference scope payload) tail
  | .recordDefault _ source fallback, result =>
      ∃ first, Lowered scope resolve source first ∧ result = .both first (reference scope fallback)
  | .variant _ payload, result => result = reference scope payload
  | .arrow input incoming output outgoing, result => result = arrow scope input incoming output outgoing
  | .mask _ source, result => Lowered scope resolve source result
  | .nominal name actuals, result => ∃ formals,
      resolve name = some formals ∧ ArgumentsLowered scope formals actuals result

theorem lower_exact (scope : Scope Index Parameter nodes types rows) (resolve : Resolver Parameter)
    (body : Body nodes types rows) (result : Expr Index Parameter) :
    lower scope resolve body = some result ↔ Lowered scope resolve body result := by
  induction body generalizing result with
  | parameter | base | float | bottom | top | emptyRecord | exactEmpty | pair | variant | arrow =>
      simp [lower, Lowered, eq_comm]
  | union first last ihFirst ihLast | inter first last ihFirst ihLast =>
      simp only [lower, combine_exact, Lowered, ihFirst, ihLast]
  | record label payload rest ih =>
      simp only [lower, Option.map_eq_some_iff, Lowered]
      constructor
      · rintro ⟨tail, compiled, rfl⟩
        exact ⟨tail, (ih tail).mp compiled, rfl⟩
      · rintro ⟨tail, lowered, rfl⟩
        exact ⟨tail, (ih tail).mpr lowered, rfl⟩
  | recordDefault label source fallback ih =>
      simp only [lower, Option.map_eq_some_iff, Lowered]
      constructor
      · rintro ⟨first, compiled, rfl⟩
        exact ⟨first, (ih first).mp compiled, rfl⟩
      · rintro ⟨first, lowered, rfl⟩
        exact ⟨first, (ih first).mpr lowered, rfl⟩
  | mask hidden source ih => exact ih result
  | nominal name actuals =>
      simp only [lower, Option.bind_eq_some_iff, Lowered, lower_arguments_exact]

theorem lower_arguments_preserves_every_kind (scope : Scope Index Parameter nodes types rows)
    (formals : Header Parameter) (actuals : List (Argument nodes types rows)) (result)
    (compiled : lowerArguments scope formals actuals = some result) :
    formals.map Prod.fst = actuals.map argumentKind := by
  have lowered := (lower_arguments_exact _ _ _ _).mp compiled
  induction formals generalizing actuals result with
  | nil => cases actuals <;> simp_all [ArgumentsLowered]
  | cons formal formals ih =>
      obtain ⟨kind, parameter⟩ := formal
      cases actuals with
      | nil => cases lowered
      | cons actual actuals =>
          obtain ⟨kindSame, rest, lowered, _⟩ := lowered
          simp only [List.map_cons, kindSame]
          congr 1
          exact ih _ _ ((lower_arguments_exact _ _ _ _).mpr lowered) lowered

end Yulang.CommonDeclarationVarianceLowering
