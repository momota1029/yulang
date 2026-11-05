import Yulang.ValueBounds

/-!
# Executable value inference for an expression fragment

The input is the existing `Inference.Expr`, with no supplied intermediate
types or constraint solution. Variables, literals, branches, lets, pairs and
variants are inferred recursively. Branches invoke the actual unknown-bound
solver, including its condition check and least output type construction.

The fragment is pure at evaluation time; environment values may still have
arbitrary structural types with signed latent effect rows. Both existing let
rules are covered, including the alternative for generalized syntactic values.
Unsupported syntax is reported separately from an untypable supported term.
Lambda/application, effect operations and source elaboration are not claimed.
-/

namespace Yulang.ValueInference

open Inference

abbrev ValueType (n : Nat) (Key : Type) := SignedStructural.Ty n Key

variable {n : Nat} {Key : Type}

inductive Result (n : Nat) (Key : Type) where
  | unsupported
  | unsat
  | solved (type : ValueType n Key)
  deriving DecidableEq

/-- This syntactic boundary does not inspect inferred types or solver success. -/
def supported : Expr → Bool
  | .var _ | .lit _ => true
  | .branch condition yes no => supported condition && supported yes && supported no
  | .letE value body | .pair value body => supported value && supported body
  | .variant _ payload => supported payload
  | _ => false

def branchProblem (condition yes no : ValueType n Key) :
    ValueBounds.Problem 1 (Directed.Row n Key) :=
  [.check condition (.base .bool), .lower yes 0, .lower no 0]

/-- The fresh output slot is actually solved, not filled by the caller. -/
def inferBranch [DecidableEq Key] (condition yes no : ValueType n Key) :
    Option (ValueType n Key) :=
  (ValueBounds.solve StructuralDecisions.checkSigned (branchProblem condition yes no)).map
    (fun value => value 0)

/-- Internal entry point; `solve` keeps unsupported syntax separate from failure. -/
def infer [DecidableEq Key] (types : List (ValueType n Key)) : Expr → Option (ValueType n Key)
  | .var index => types[index]?
  | .lit base => some (.base base)
  | .branch condition yes no =>
      (infer types condition).bind fun conditionType =>
      (infer types yes).bind fun yesType =>
      (infer types no).bind fun noType =>
        inferBranch conditionType yesType noType
  | .letE value body =>
      (infer types value).bind fun valueType => infer (valueType :: types) body
  | .pair left right =>
      (infer types left).bind fun leftType =>
      (infer types right).bind fun rightType => some (.pair leftType rightType)
  | .variant label payload =>
      (infer types payload).bind fun payloadType => some (.variant label payloadType)
  | _ => none

def solve [DecidableEq Key] (types : List (ValueType n Key)) (expression : Expr) : Result n Key :=
  if supported expression then
    match infer types expression with
    | none => .unsat
    | some type => .solved type
  else .unsupported

/-- Each source binding denotes exactly the supertypes of its inferred value
type. Its evaluation is pure; latent rows inside that type are unrestricted. -/
def EnvPrincipal (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key))) : Prop :=
  ∀ index result,
    BindingLookup (SignedStructural.model n Key) bindings index result ↔
      ∃ type, types[index]? = some type ∧ SignedStructural.Subtype type result.1

private def EnvLower (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key))) : Prop :=
  ∀ index result, BindingLookup (SignedStructural.model n Key) bindings index result →
    ∃ type, types[index]? = some type ∧ SignedStructural.Subtype type result.1

private def EnvUpper (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key))) : Prop :=
  ∀ index result type, types[index]? = some type → SignedStructural.Subtype type result.1 →
    BindingLookup (SignedStructural.model n Key) bindings index result

private theorem lower_of_principal {types : List (ValueType n Key)}
    {bindings : List (Binding (SignedStructural.model n Key))}
    (environment : EnvPrincipal types bindings) : EnvLower types bindings :=
  fun index result => (environment index result).mp

private theorem upper_of_principal {types : List (ValueType n Key)}
    {bindings : List (Binding (SignedStructural.model n Key))}
    (environment : EnvPrincipal types bindings) : EnvUpper types bindings :=
  fun index result type found subtype => (environment index result).mpr ⟨type, found, subtype⟩

theorem envPrincipal_nil : EnvPrincipal ([] : List (ValueType n Key)) [] := by
  intro index result
  simp [BindingLookup]

private theorem envUpper_mono {types : List (ValueType n Key)}
    {bindings : List (Binding (SignedStructural.model n Key))}
    (environment : EnvUpper types bindings) (type : ValueType n Key) :
    EnvUpper (type :: types) (.mono (type, []) :: bindings) := by
  intro index result chosen found subtype
  cases index with
  | zero =>
      have equal : type = chosen := Option.some.inj found
      subst chosen
      exact ⟨_, rfl, .mono ⟨subtype, SignedStructural.row_bottom _⟩⟩
  | succ index =>
      obtain ⟨binding, member, typed⟩ := environment index result chosen found subtype
      exact ⟨binding, member, typed⟩

private theorem envLower_cons {types : List (ValueType n Key)}
    {bindings : List (Binding (SignedStructural.model n Key))}
    (environment : EnvLower types bindings) (type : ValueType n Key)
    (binding : Binding (SignedStructural.model n Key))
    (head : ∀ result, BindingTyping (SignedStructural.model n Key) binding result →
      SignedStructural.Subtype type result.1) : EnvLower (type :: types) (binding :: bindings) := by
  intro index result lookup
  obtain ⟨chosen, found, typed⟩ := lookup
  cases index with
  | zero =>
      have equal : binding = chosen := Option.some.inj found
      subst chosen
      exact ⟨type, rfl, head result typed⟩
  | succ index =>
      obtain ⟨type, foundType, subtype⟩ := environment index result ⟨chosen, found, typed⟩
      exact ⟨type, foundType, subtype⟩

theorem inferBranch_exact [DecidableEq Key] (condition yes no upper : ValueType n Key) :
    (∃ type, inferBranch condition yes no = some type ∧ SignedStructural.Subtype type upper) ↔
      SignedStructural.Subtype condition (.base .bool) ∧
      SignedStructural.Subtype yes upper ∧ SignedStructural.Subtype no upper := by
  constructor
  · rintro ⟨type, found, below⟩
    obtain ⟨value, solved, equal⟩ := Option.map_eq_some_iff.mp found
    have model := ValueBounds.solve_sound StructuralDecisions.checkSigned
      StructuralDecisions.checkSigned_exact solved
    have conditionBound := model (.check condition (.base .bool)) (by simp [branchProblem])
    have yesBound := model (.lower yes 0) (by simp [branchProblem])
    have noBound := model (.lower no 0) (by simp [branchProblem])
    change value 0 = type at equal
    subst type
    exact ⟨conditionBound, .trans yesBound below, .trans noBound below⟩
  · rintro ⟨conditionBound, yesBound, noBound⟩
    have model : ValueBounds.Models SignedStructural.RowLe (branchProblem condition yes no)
        (fun _ => upper) := by
      intro constraint member
      simp only [branchProblem, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionBound
      · exact yesBound
      · exact noBound
    have leastModel := ValueBounds.least_models_of_models model
    have solved := (ValueBounds.solve_some_iff StructuralDecisions.checkSigned
      StructuralDecisions.checkSigned_exact (branchProblem condition yes no)
      (ValueBounds.least (branchProblem condition yes no))).mpr ⟨rfl, leastModel⟩
    refine ⟨_, ?_, ValueBounds.least_below model.lower 0⟩
    simp only [inferBranch, solved, Option.map_some]

private theorem infer_sound_aux [DecidableEq Key] (expression : Expr)
    (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvUpper types bindings) (type : ValueType n Key)
    (found : infer types expression = some type)
    (result : Comp (SignedStructural.model n Key))
    (below : SignedStructural.Subtype type result.1) :
    Typing (SignedStructural.model n Key) bindings expression result := by
  induction expression generalizing types bindings type result with
  | var index =>
      obtain ⟨binding, member, typed⟩ := environment index result type found below
      exact .var member typed
  | lit base =>
      have same : StructuralBase.Ty.base base = type := Option.some.inj found
      subst type
      exact .lit ⟨below, SignedStructural.row_bottom _⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      simp only [infer, Option.bind_eq_some_iff] at found
      obtain ⟨conditionType, conditionFound, yesType, yesFound, noType, noFound, joined⟩ := found
      obtain ⟨conditionBound, yesBound, noBound⟩ :=
        (inferBranch_exact conditionType yesType noType type).mp ⟨type, joined, .refl _⟩
      exact .branch
        (ihCondition types bindings environment conditionType conditionFound
          (.base .bool, []) conditionBound)
        (ihYes types bindings environment yesType yesFound (yesType, []) (.refl _))
        (ihNo types bindings environment noType noFound (noType, []) (.refl _))
        ⟨.unionElim (.trans yesBound below) (.trans noBound below), SignedStructural.row_bottom _⟩
  | letE value body ihValue ihBody =>
      simp only [infer, Option.bind_eq_some_iff] at found
      obtain ⟨valueType, valueFound, bodyFound⟩ := found
      exact .letComputed
        (ihValue types bindings environment valueType valueFound (valueType, []) (.refl _))
        (ihBody (valueType :: types) (.mono (valueType, []) :: bindings)
          (envUpper_mono environment valueType) type bodyFound result below)
        ⟨.refl _, SignedStructural.row_refl _⟩
  | pair left right ihLeft ihRight =>
      simp only [infer, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨leftType, leftFound, rightType, rightFound, same⟩ := found
      subst type
      exact .pair
        (ihLeft types bindings environment leftType leftFound (leftType, []) (.refl _))
        (ihRight types bindings environment rightType rightFound (rightType, []) (.refl _))
        ⟨below, SignedStructural.row_bottom _⟩
  | variant label payload ihPayload =>
      simp only [infer, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨payloadType, payloadFound, same⟩ := found
      subst type
      exact .variant
        (ihPayload types bindings environment payloadType payloadFound (payloadType, []) (.refl _))
        ⟨below, SignedStructural.row_bottom _⟩
  | _ => simp [infer] at found

private theorem infer_complete_aux [DecidableEq Key] (expression : Expr)
    (supportedExpression : supported expression = true)
    (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvLower types bindings)
    (result : Comp (SignedStructural.model n Key))
    (typed : Typing (SignedStructural.model n Key) bindings expression result) :
    ∃ type, infer types expression = some type ∧ SignedStructural.Subtype type result.1 := by
  induction expression generalizing types bindings result with
  | var index =>
      cases typed with
      | var found bindingTyped =>
          obtain ⟨type, foundType, below⟩ := environment index result ⟨_, found, bindingTyped⟩
          exact ⟨type, foundType, below⟩
  | lit base =>
      cases typed with
      | lit below => exact ⟨.base base, rfl, below.1⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      simp only [supported, Bool.and_eq_true] at supportedExpression
      cases typed with
      | branch conditionTyped yesTyped noTyped below =>
          obtain ⟨conditionType, conditionFound, conditionBound⟩ :=
            ihCondition supportedExpression.1.1 types bindings environment _ conditionTyped
          obtain ⟨yesType, yesFound, yesBound⟩ :=
            ihYes supportedExpression.1.2 types bindings environment _ yesTyped
          obtain ⟨noType, noFound, noBound⟩ :=
            ihNo supportedExpression.2 types bindings environment _ noTyped
          have yesBelow := StructuralBase.Subtype.trans yesBound
            (StructuralBase.Subtype.trans (StructuralBase.Subtype.unionLeft _ _) below.1)
          have noBelow := StructuralBase.Subtype.trans noBound
            (StructuralBase.Subtype.trans (StructuralBase.Subtype.unionRight _ _) below.1)
          obtain ⟨type, joined, finalBound⟩ :=
            (inferBranch_exact conditionType yesType noType result.1).mpr
              ⟨conditionBound, yesBelow, noBelow⟩
          exact ⟨type, by simp only [infer, conditionFound, yesFound, noFound,
            Option.bind_some, joined], finalBound⟩
  | letE value body ihValue ihBody =>
      simp only [supported, Bool.and_eq_true] at supportedExpression
      cases typed with
      | letValue isValue valueTyped bodyTyped =>
          obtain ⟨valueType, valueFound, _⟩ :=
            ihValue supportedExpression.1 types bindings environment _ valueTyped
          have bodyEnvironment : EnvLower (valueType :: types) (.poly value bindings :: bindings) := by
            apply envLower_cons environment valueType (.poly value bindings)
            intro result bindingTyped
            cases bindingTyped with
            | poly anotherTyped _ =>
                obtain ⟨another, anotherFound, anotherBound⟩ :=
                  ihValue supportedExpression.1 types bindings environment _ anotherTyped
                have same : valueType = another := Option.some.inj (valueFound.symm.trans anotherFound)
                subst another
                exact anotherBound
          obtain ⟨type, bodyFound, below⟩ :=
            ihBody supportedExpression.2 (valueType :: types)
              (.poly value bindings :: bindings) bodyEnvironment result bodyTyped
          exact ⟨type, by simp only [infer, valueFound, Option.bind_some, bodyFound], below⟩
      | @letComputed _ _ actualValue _ actualBody _ valueTyped bodyTyped below =>
          obtain ⟨valueType, valueFound, valueBound⟩ :=
            ihValue supportedExpression.1 types bindings environment _ valueTyped
          have bodyEnvironment : EnvLower (valueType :: types)
              (.mono (Comp.pure (SignedStructural.model n Key) actualValue.1) :: bindings) := by
            apply envLower_cons environment valueType _
            intro result bindingTyped
            cases bindingTyped with
            | mono actualBound => exact .trans valueBound actualBound.1
          obtain ⟨type, bodyFound, bodyBound⟩ :=
            ihBody supportedExpression.2 (valueType :: types) _ bodyEnvironment _ bodyTyped
          exact ⟨type, by simp only [infer, valueFound, Option.bind_some, bodyFound],
            .trans bodyBound below.1⟩
  | pair left right ihLeft ihRight =>
      simp only [supported, Bool.and_eq_true] at supportedExpression
      cases typed with
      | pair leftTyped rightTyped below =>
          obtain ⟨leftType, leftFound, leftBound⟩ :=
            ihLeft supportedExpression.1 types bindings environment _ leftTyped
          obtain ⟨rightType, rightFound, rightBound⟩ :=
            ihRight supportedExpression.2 types bindings environment _ rightTyped
          exact ⟨.pair leftType rightType,
            by simp only [infer, leftFound, rightFound, Option.bind_some],
            .trans (.pair leftBound rightBound) below.1⟩
  | variant label payload ihPayload =>
      cases typed with
      | variant payloadTyped below =>
          obtain ⟨payloadType, payloadFound, payloadBound⟩ :=
            ihPayload supportedExpression types bindings environment _ payloadTyped
          exact ⟨.variant label payloadType,
            by simp only [infer, payloadFound, Option.bind_some],
            .trans (.variant payloadBound) below.1⟩
  | _ => simp [supported] at supportedExpression

/-- No expected result type is needed to infer the least value type. Every
declarative result is exactly a supertype of the computed answer. -/
theorem infer_principal [DecidableEq Key] (expression : Expr)
    (supportedExpression : supported expression = true)
    (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvPrincipal types bindings)
    (result : Comp (SignedStructural.model n Key)) :
    (∃ type, infer types expression = some type ∧ SignedStructural.Subtype type result.1) ↔
      Typing (SignedStructural.model n Key) bindings expression result := by
  constructor
  · rintro ⟨type, found, below⟩
    exact infer_sound_aux expression types bindings (upper_of_principal environment)
      type found result below
  · exact infer_complete_aux expression supportedExpression types bindings
      (lower_of_principal environment) result

theorem solve_solved_iff [DecidableEq Key] (types : List (ValueType n Key))
    (expression : Expr) (type : ValueType n Key) :
    solve types expression = .solved type ↔
      supported expression = true ∧ infer types expression = some type := by
  unfold solve
  split
  · rename_i supportedExpression
    cases infer types expression <;> simp [supportedExpression]
  · rename_i unsupportedExpression
    simp [unsupportedExpression]

theorem solve_unsupported_iff [DecidableEq Key] (types : List (ValueType n Key))
    (expression : Expr) :
    solve types expression = .unsupported ↔ supported expression = false := by
  unfold solve
  split
  · rename_i supportedExpression
    cases infer types expression <;> simp [supportedExpression]
  · rename_i unsupportedExpression
    simp only [Bool.not_eq_true] at unsupportedExpression
    simp [unsupportedExpression]

theorem solve_principal [DecidableEq Key] (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvPrincipal types bindings) (expression : Expr) (type : ValueType n Key)
    (returned : solve types expression = .solved type)
    (result : Comp (SignedStructural.model n Key)) :
    Typing (SignedStructural.model n Key) bindings expression result ↔
      SignedStructural.Subtype type result.1 := by
  obtain ⟨supportedExpression, found⟩ := (solve_solved_iff types expression type).mp returned
  rw [← infer_principal expression supportedExpression types bindings environment result]
  simp [found]

theorem solve_sound [DecidableEq Key] (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvPrincipal types bindings) (expression : Expr) (type : ValueType n Key)
    (returned : solve types expression = .solved type) :
    Typing (SignedStructural.model n Key) bindings expression (type, []) :=
  (solve_principal types bindings environment expression type returned (type, [])).mpr (.refl _)

/-- Unsatisfiability ranges over every structural result type and every signed
effect row, not merely the finite intermediates used during this run. -/
theorem solve_unsat_iff [DecidableEq Key] (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvPrincipal types bindings) (expression : Expr)
    (supportedExpression : supported expression = true) :
    solve types expression = .unsat ↔
      ¬ ∃ result, Typing (SignedStructural.model n Key) bindings expression result := by
  cases found : infer types expression with
  | none =>
      constructor
      · intro _ ⟨result, typed⟩
        obtain ⟨type, returned, _⟩ :=
          (infer_principal expression supportedExpression types bindings environment result).mpr typed
        rw [found] at returned
        cases returned
      · intro _
        simp [solve, supportedExpression, found]
  | some type =>
      have returned : solve types expression = .solved type :=
        (solve_solved_iff types expression type).mpr ⟨supportedExpression, found⟩
      have typed := solve_sound types bindings environment expression type returned
      simp only [returned, reduceCtorEq, false_iff]
      exact fun impossible => impossible ⟨(type, []), typed⟩

/-- A concrete input environment of known values automatically satisfies the
environment contract; clients do not supply a solution of expression constraints. -/
def monoEnvironment (types : List (ValueType n Key)) : List (Binding (SignedStructural.model n Key)) :=
  types.map fun type => .mono (type, [])

theorem monoEnvironment_principal (types : List (ValueType n Key)) :
    EnvPrincipal types (monoEnvironment types) := by
  induction types with
  | nil => exact envPrincipal_nil
  | cons type types ih =>
      have lower : EnvLower (type :: types) (monoEnvironment (type :: types)) := by
        apply envLower_cons (lower_of_principal ih) type (.mono (type, []))
        intro result typed
        cases typed with
        | mono below => exact below.1
      have upper : EnvUpper (type :: types) (monoEnvironment (type :: types)) :=
        envUpper_mono (upper_of_principal ih) type
      intro index result
      exact ⟨lower index result,
        fun ⟨chosen, member, below⟩ => upper index result chosen member below⟩

theorem source_solved_exact [DecidableEq Key] (types : List (ValueType n Key))
    (expression : Expr) (type : ValueType n Key)
    (returned : solve types expression = .solved type)
    (result : Comp (SignedStructural.model n Key)) :
    Typing (SignedStructural.model n Key) (monoEnvironment types) expression result ↔
      SignedStructural.Subtype type result.1 :=
  solve_principal types (monoEnvironment types) (monoEnvironment_principal types)
    expression type returned result

theorem source_unsat_iff [DecidableEq Key] (types : List (ValueType n Key))
    (expression : Expr) (supportedExpression : supported expression = true) :
    solve types expression = .unsat ↔
      ¬ ∃ result, Typing (SignedStructural.model n Key) (monoEnvironment types) expression result :=
  solve_unsat_iff types (monoEnvironment types) (monoEnvironment_principal types)
    expression supportedExpression

/-- This is the original generated formula, including all fresh existential
slots and the `or` between value-let and monomorphic-let. No formula-solution
certificate is a premise. -/
theorem principal_solved_exact [DecidableEq Key] (types : List (ValueType n Key))
    (bindings : List (Binding (SignedStructural.model n Key)))
    (environment : EnvPrincipal types bindings) (schemes : SchemeEnv α)
    (assignment : α → Comp (SignedStructural.model n Key))
    (related : EnvRel (SignedStructural.model n Key) assignment schemes bindings)
    (expression : Expr) (type : ValueType n Key)
    (returned : solve types expression = .solved type)
    (result : Comp (SignedStructural.model n Key)) :
    (principal schemes expression).Holds (SignedStructural.model n Key) (extend assignment result) ↔
      SignedStructural.Subtype type result.1 :=
  (principal_exact _ expression schemes bindings assignment related result).trans
    (solve_principal types bindings environment expression type returned result)

theorem closed_principal_solved_exact [DecidableEq Key] (expression : Expr) (type : ValueType n Key)
    (returned : solve [] expression = .solved type)
    (result : Comp (SignedStructural.model n Key)) :
    (principal ([] : SchemeEnv Empty) expression).Holds (SignedStructural.model n Key)
      (extend Empty.elim result) ↔ SignedStructural.Subtype type result.1 :=
  principal_solved_exact [] [] envPrincipal_nil [] Empty.elim (EnvRel.nil _ _)
    expression type returned result

theorem closed_principal_unsat_iff [DecidableEq Key] (expression : Expr)
    (supportedExpression : supported expression = true) :
    solve (n := n) (Key := Key) [] expression = .unsat ↔
      ¬ ∃ result, (principal ([] : SchemeEnv Empty) expression).Holds
        (SignedStructural.model n Key) (extend Empty.elim result) := by
  rw [solve_unsat_iff [] [] envPrincipal_nil expression supportedExpression]
  apply not_congr
  apply exists_congr
  intro result
  exact (principal_exact _ expression [] [] Empty.elim (EnvRel.nil _ _) result).symm

end Yulang.ValueInference
