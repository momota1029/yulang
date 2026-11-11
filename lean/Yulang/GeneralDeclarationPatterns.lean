import Yulang.CheckedRoles
import Yulang.GeneralNormalizedObservation
import Yulang.VariantsMerged

/-!
# Finite declaration patterns and normalization before counting

Constructor applications retain resolved names and arbitrary arities; they are
not restricted to scalar or unary types. A constructor catalogue can retain
nominal variance, row and interval layouts without unfolding named bodies.
Records and variant joins have explicit nodes so invisible source padding is
removed before any count. This finite pattern normalizer is not a complete
decision procedure for Common equivalence or recursive source materialization.
-/
namespace Yulang.GeneralDeclarationPatterns

inductive Pattern where
  | var (name : Nat)
  | app (constructor : Nat) (arguments : List Pattern)
  | record (label : Nat) (payload tail : Pattern)
  | variant (tag : Nat) (payload : Pattern)
  | join (first last : Pattern)
  deriving Repr

mutual
  def Pattern.decEq (first last : Pattern) : Decidable (first = last) := by
    cases first <;> cases last
    case var.var a b => exact decidable_of_iff (a = b) (by simp)
    case app.app a xs b ys =>
      letI := argsDecEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp)
    case record.record a x xs b y ys =>
      letI := Pattern.decEq x y
      letI := Pattern.decEq xs ys
      exact decidable_of_iff (a = b ∧ x = y ∧ xs = ys) (by simp)
    case variant.variant a x b y =>
      letI := Pattern.decEq x y
      exact decidable_of_iff (a = b ∧ x = y) (by simp)
    case join.join x xs y ys =>
      letI := Pattern.decEq x y
      letI := Pattern.decEq xs ys
      exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
    all_goals exact isFalse (by intro h; cases h)
  def argsDecEq (first last : List Pattern) : Decidable (first = last) := by
    cases first with
    | nil => cases last <;> exact inferInstance
    | cons a xs =>
      cases last with
      | nil => exact isFalse (by intro h; cases h)
      | cons b ys =>
        letI := Pattern.decEq a b
        letI := argsDecEq xs ys
        exact decidable_of_iff (a = b ∧ xs = ys) (by simp)
end

instance : DecidableEq Pattern := Pattern.decEq

/-- The catalogue describes resolved constructors, including the complete
type/row/interval argument layout. It does not assign nominal bodies. -/
inductive ParameterKind where
  | type | row | lower | upper
  deriving Repr, DecidableEq

structure Constructor where
  parameters : List ParameterKind
  name : Nat

abbrev Constructors := Nat → Option Constructor

mutual
  def Pattern.encode : Pattern → Roles.Term
    | .var name => .var name
    | .app constructor arguments => .app (4 * constructor) (encodeArgs arguments)
    | .record label payload tail => .app (4 * label + 1) [payload.encode, tail.encode]
    | .variant tag payload => .app (4 * tag + 2) [payload.encode]
    | .join first last => .app 3 [first.encode, last.encode]
  def encodeArgs : List Pattern → List Roles.Term
    | [] => []
    | first :: rest => first.encode :: encodeArgs rest
end

mutual
  def Pattern.subst (capture : Nat → Pattern) : Pattern → Pattern
    | .var name => capture name
    | .app constructor arguments => .app constructor (substArgs capture arguments)
    | .record label payload tail => .record label (payload.subst capture) (tail.subst capture)
    | .variant tag payload => .variant tag (payload.subst capture)
    | .join first last => .join (first.subst capture) (last.subst capture)
  def substArgs (capture : Nat → Pattern) : List Pattern → List Pattern
    | [] => []
    | first :: rest => first.subst capture :: substArgs capture rest
end

/-- Remove a hidden field only along the record spine. Payload visibility
starts afresh; an unknown tail remains the same variable. -/
def hide (label : Nat) : Pattern → Pattern
  | .record current payload tail =>
      if label = current then hide label tail else .record current payload (hide label tail)
  | other => other

def variantRow : Pattern → Option (List (Nat × Pattern))
  | .variant tag payload => some [(tag, payload)]
  | .join first last => do return (← variantRow first) ++ (← variantRow last)
  | _ => none

def rowPattern : List (Nat × Pattern) → Pattern
  | [] => .app 0 []
  | [(tag, payload)] => .variant tag payload
  | (tag, payload) :: rest => .join (.variant tag payload) (rowPattern rest)

def mergePayload (first last : Pattern) : Pattern :=
  if first = last then first else .join first last

/-- Group the whole variant row, including separated occurrences of a tag.
Remaining payload joins retain their data and require further coverage. -/
def merge (first last : Pattern) : Pattern :=
  if first = last then first else
  match variantRow first, variantRow last with
  | some xs, some ys => rowPattern
      ((Variants.Merged.normalize mergePayload (xs ++ ys)).entries.mergeSort (fun a b => a.1 ≤ b.1))
  | _, _ => .join first last

mutual
  def normalize : Pattern → Pattern
    | .var name => .var name
    | .app constructor arguments => .app constructor (normalizeArgs arguments)
    | .record label payload tail => .record label (normalize payload) (hide label (normalize tail))
    | .variant tag payload => .variant tag (normalize payload)
    | .join first last => merge (normalize first) (normalize last)
  def normalizeArgs : List Pattern → List Pattern
    | [] => []
    | first :: rest => normalize first :: normalizeArgs rest
end

def counted (arguments : List Pattern) : List Roles.Term := encodeArgs (normalizeArgs arguments)

mutual
  def covered : Pattern → Bool
    | .var _ => true
    | .app _ arguments => coveredArgs arguments
    | .record _ payload tail => covered payload && covered tail
    | .variant _ payload => covered payload
    | .join _ _ => false
  def coveredArgs : List Pattern → Bool
    | [] => true
    | first :: rest => covered first && coveredArgs rest
end

/-- Residual joins are coverage gaps, not evidence of a language error.
Only complete counts may certify a declaration with children. -/
def CountsCovered (head child : List Pattern) : Prop :=
  coveredArgs (normalizeArgs head) = true ∧ coveredArgs (normalizeArgs child) = true

mutual
  def lower : Pattern → Roles.Term
    | .var name => .var name
    | .app constructor arguments => .app (4 * constructor) (lowerArgs arguments)
    | .record label payload _ => .app (4 * label + 1) [lower payload, .app 0 []]
    | .variant tag payload => .app (4 * tag + 2) [lower payload]
    | .join _ _ => .app 0 []
  def lowerArgs : List Pattern → List Roles.Term
    | [] => []
    | first :: rest => lower first :: lowerArgs rest
end

/-- An additional conservative check prevents counting an arbitrary open
record tail or a residual merge as guaranteed head structure. -/
def ConservativeSmaller (head child : List Pattern) : Prop :=
  CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0, counted child⟩ = true

def Smaller (head child : List Pattern) : Prop :=
  Roles.argsSize (counted child) < Roles.argsSize (counted head) ∧
    ∀ name, Roles.argsOccurrences name (counted child) ≤ Roles.argsOccurrences name (counted head)

def checkSmaller (head child : List Pattern) : Bool :=
  CheckedRoles.checkCondition (counted head) ⟨0, counted child⟩

theorem checkSmaller_exact (head child : List Pattern) :
    checkSmaller head child = true ↔ Smaller head child :=
  CheckedRoles.checkCondition_exact _ _

/-- Independent stability requirement, quantified over all finite captures.
It rejects a late merge when that merge destroys the required descent.
This is a proposition, not a claimed finite algorithm for the full language. -/
def StableSmaller (head child : List Pattern) : Prop :=
  ∀ capture : Nat → Pattern, Smaller (substArgs capture head) (substArgs capture child)

mutual
  def Pattern.variables : Pattern → List Nat
    | .var name => [name]
    | .app _ arguments => variablesArgs arguments
    | .record _ payload tail => payload.variables ++ tail.variables
    | .variant _ payload => payload.variables
    | .join first last => first.variables ++ last.variables
  def variablesArgs : List Pattern → List Nat
    | [] => []
    | first :: rest => first.variables ++ variablesArgs rest
end

/- Generic scope-resolved constructor validation. Row/type kind checking is
a separate source elaboration obligation; the layout is retained in the table. -/
mutual
  def WellScoped (constructors : Constructors) : Pattern → Prop
    | .var _ => True
    | .app name arguments =>
        (∃ declaration, constructors name = some declaration ∧ declaration.parameters.length = arguments.length) ∧
          ArgsWellScoped constructors arguments
    | .record _ payload tail => WellScoped constructors payload ∧ WellScoped constructors tail
    | .variant _ payload => WellScoped constructors payload
    | .join first last => WellScoped constructors first ∧ WellScoped constructors last
  def ArgsWellScoped (constructors : Constructors) : List Pattern → Prop
    | [] => True
    | first :: rest => WellScoped constructors first ∧ ArgsWellScoped constructors rest
end

mutual
  theorem subst_congr (pattern : Pattern) (first last : Nat → Pattern)
      (agree : ∀ name ∈ pattern.variables, first name = last name) :
      pattern.subst first = pattern.subst last := by
    cases pattern with
    | var name => exact agree name (by simp [Pattern.variables])
    | app name arguments => exact congrArg (Pattern.app name) (substArgs_congr arguments first last agree)
    | record label payload tail =>
        simp only [Pattern.subst]
        rw [subst_congr payload first last (fun name member => agree name (List.mem_append_left _ member)),
          subst_congr tail first last (fun name member => agree name (List.mem_append_right _ member))]
    | variant tag payload => exact congrArg (Pattern.variant tag) (subst_congr payload first last agree)
    | join a b =>
        simp only [Pattern.subst]
        rw [subst_congr a first last (fun name member => agree name (List.mem_append_left _ member)),
          subst_congr b first last (fun name member => agree name (List.mem_append_right _ member))]
  theorem substArgs_congr (arguments : List Pattern) (first last : Nat → Pattern)
      (agree : ∀ name ∈ variablesArgs arguments, first name = last name) :
      substArgs first arguments = substArgs last arguments := by
    cases arguments with
    | nil => rfl
    | cons pattern rest =>
        simp only [substArgs]
        rw [subst_congr pattern first last (fun name member => agree name (List.mem_append_left _ member)),
          substArgs_congr rest first last (fun name member => agree name (List.mem_append_right _ member))]
end

theorem hide_idempotent (label : Nat) (pattern : Pattern) :
    hide label (hide label pattern) = hide label pattern := by
  cases pattern with
  | record current payload rest =>
      have ih := hide_idempotent label rest
      by_cases same : label = current <;> simp_all [hide]
  | _ => rfl

theorem hidden_field_removed (label : Nat) (payload hidden tail : Pattern) :
    normalize (.record label payload (.record label hidden tail)) =
      normalize (.record label payload tail) := by
  simp [normalize, hide, hide_idempotent]

theorem duplicate_variant_removed (tag : Nat) (payload : Pattern) :
    normalize (.join (.variant tag payload) (.variant tag payload)) = normalize (.variant tag payload) := by
  simp [normalize, merge]

/-- This schema covers any resolved nominal constructor, with any finite
captured payload, including payloads needing record/tag normalization. -/
theorem unary_descent (constructor name : Nat) :
    StableSmaller [.app constructor [.var name]] [.var name] := by
  intro capture
  constructor
  · simp [counted, substArgs, Pattern.subst, normalizeArgs, normalize,
      encodeArgs, Pattern.encode, Roles.argsSize, Roles.Term.size]
  · intro name
    simp [counted, substArgs, Pattern.subst, normalizeArgs, normalize,
      encodeArgs, Pattern.encode, Roles.argsOccurrences, Roles.Term.occurrences]

end Yulang.GeneralDeclarationPatterns
