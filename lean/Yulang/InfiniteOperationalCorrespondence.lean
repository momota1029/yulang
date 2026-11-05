import Yulang.OperationalCorrespondence
import Yulang.InfiniteRowHygiene

/-!
# Generated constraints bound runtime requests by possibly infinite rows

This module interprets the existing recursive generator in `RecursiveRows.SetRow`.
It shares `StructuralBase` value types, `OperationalCorrespondence.erase` and
`principal`, and the original `OperationalTyping.Expr` and `eval`; no alternate
execution or permission semantics is introduced. Infinite rows have no finite
support, enumeration or depth-cap premise.

The fundamental theorem derives both request bounds and returned-value validity
from every typing derivation of the erased resolved fragment, including union,
intersection, arrows and both value-restricted binding rules. Handler action and
arm bounds are conclusions of this interpretation, not additional premises.
A solution of the very same generated principal formula therefore bounds the
same runtime expression and supplies the fresh-boundary noncapture theorem.

This is semantic soundness for a supplied constraint solution, not an infinite
row checker or a completeness theorem for a solver. Runtime shapes are already
resolved. Opaque atoms, operation payloads and responses share one carrier,
interpreted by the structural `unit` base. Source elaboration, heterogeneous
operation signatures, recursion in runtime expressions and type-directed
latent-value wrappers remain outside this fragment; boundaries transform
immediate requests only.
-/

namespace Yulang.InfiniteOperationalCorrespondence

open Directed OperationalTyping
open RecursiveRows (SetRow algebra)
open InfiniteRowHygiene (Included emptyRow joinRow residualRow BoundedBy)
open OperationalCorrespondence (varIndex erase signatureTerms principal)

abbrev Model (n : Nat) (Key : Type) :=
  StructuralBase.model (SetRow n Key) emptyRow joinRow Included
abbrev CoreType (n : Nat) (Key : Type) := StructuralBase.Ty (SetRow n Key)
abbrev CoreComp (n : Nat) (Key : Type) := CoreType n Key × SetRow n Key
abbrev CoreBinding (n : Nat) (Key : Type) :=
  RecursiveEffects.Binding (Model n Key) Key Key (Fin n)

/-- The structural and row calculi use the identical possibly infinite row. -/
def rowView (n : Nat) (Key : Type) : RowInference.RowView (Model n Key) (algebra n Key) where
  decode := id
  decode_empty := rfl
  decode_join := fun _ _ => rfl
  subtype_iff := fun _ _ => Iff.rfl

def signatures (n : Nat) (Key : Type) (key : Key) :
    RecursiveEffects.Signature (Model n Key) Key :=
  ⟨key, [], .base .unit, .base .unit⟩

abbrev CoreTyping {n : Nat} {Key : Type} :=
  RecursiveEffects.Typing (Model n Key) (rowView n Key) (signatures n Key)

abbrev CoreBindingTyping {n : Nat} {Key : Type} :=
  RecursiveEffects.BindingTyping (Model n Key) (rowView n Key) (signatures n Key)

theorem join_empty (row : SetRow n Key) : joinRow row emptyRow = row := by
  funext occurrence
  exact or_false (row occurrence)

theorem empty_join (row : SetRow n Key) : joinRow emptyRow row = row := by
  funext occurrence
  exact false_or (row occurrence)

private theorem bounded_mono {left right : SetRow n Key}
    (included : Included left right) {computation : Computation n Key Payload Response A}
    (bound : BoundedBy left computation) : BoundedBy right computation :=
  InfiniteRowHygiene.bounded_mono left right included computation bound

/-- Sequential composition uses set union, with no finiteness restriction on
request branching or the rows supplied by either computation. -/
theorem bind_bounds_returns (left right : SetRow n Key) (source : A → Prop) (target : B → Prop)
    (computation : Computation n Key Payload Response A)
    (next : A → Computation n Key Payload Response B)
    (bounded : BoundedBy left computation)
    (returned : AllReturns source computation)
    (nextValid : ∀ value, source value →
      BoundedBy right (next value) ∧ AllReturns target (next value)) :
    BoundedBy (joinRow left right) (computation.bind next) ∧
      AllReturns target (computation.bind next) := by
  induction computation with
  | pure value =>
      have good := nextValid value returned
      exact ⟨bounded_mono (fun _ member => Or.inr member) good.1, good.2⟩
  | request occurrence payload resume ih =>
      refine ⟨⟨Or.inl bounded.1, ?_⟩, ?_⟩
      · intro response
        exact (ih response (bounded.2 response) (returned response)).1
      · intro response
        exact (ih response (bounded.2 response) (returned response)).2

/-- Structural types are interpreted at the already resolved runtime shape.
Records and variants have no values in this fragment, while unions and
intersections retain their ordinary disjunctive/conjunctive interpretation. -/
def TypeHolds : CoreType n Key → (shape : Shape) → Value n Key Atom shape → Prop
  | .base base, .atom, _ => base = .unit
  | .base _, .pair _ _, _ => False
  | .base _, .arrow _ _, _ => False
  | .bottom, _, _ => False
  | .union a b, shape, value => TypeHolds a shape value ∨ TypeHolds b shape value
  | .inter a b, shape, value => TypeHolds a shape value ∧ TypeHolds b shape value
  | .pair a b, .pair left right, value => TypeHolds a left value.1 ∧ TypeHolds b right value.2
  | .pair _ _, .atom, _ => False
  | .pair _ _, .arrow _ _, _ => False
  | .emptyRecord, _, _ => False
  | .record _ _ _, _, _ => False
  | .variant _ _, _, _ => False
  | .arrow a ea b eb, .arrow domain codomain, function =>
      ∀ argument, BoundedBy ea argument → AllReturns (TypeHolds a domain) argument →
        BoundedBy eb (function argument) ∧
          AllReturns (TypeHolds b codomain) (function argument)
  | .arrow _ _ _ _, .atom, _ => False
  | .arrow _ _ _ _, .pair _ _, _ => False

def CompHolds (type : CoreComp n Key) (computation : Tree n Key Atom shape) : Prop :=
  BoundedBy type.2 computation ∧ AllReturns (TypeHolds type.1 shape) computation

theorem record_has_no_values {type : CoreType n Key} (record : StructuralBase.IsRecord type)
    (shape : Shape) (value : Value n Key Atom shape) : ¬ TypeHolds type shape value := by
  cases record <;> simp [TypeHolds]

theorem subtype_interpretation {left right : CoreType n Key}
    (subtype : StructuralBase.Subtype Included left right) (shape : Shape)
    (value : Value n Key Atom shape) (valid : TypeHolds left shape value) :
    TypeHolds right shape value := by
  induction subtype generalizing shape with
  | refl => exact valid
  | trans _ _ ihl ihr => exact ihr shape value (ihl shape value valid)
  | bottom => exact False.elim valid
  | unionLeft => exact Or.inl valid
  | unionRight => exact Or.inr valid
  | unionElim _ _ ihl ihr => exact valid.elim (ihl shape value) (ihr shape value)
  | interLeft => exact valid.1
  | interRight => exact valid.2
  | interIntro _ _ ihl ihr => exact ⟨ihl shape value valid, ihr shape value valid⟩
  | pair ha hb iha ihb =>
      cases shape with
      | atom => exact False.elim valid
      | arrow _ _ => exact False.elim valid
      | pair a b =>
          exact ⟨iha a value.1 valid.1, ihb b value.2 valid.2⟩
  | variant => exact False.elim valid
  | arrow hi inputRow ho outputRow ihi iho =>
      cases shape with
      | atom => exact False.elim valid
      | pair _ _ => exact False.elim valid
      | arrow domain codomain =>
          intro argument bounded returned
          have oldInput := allReturns_mono _ _ (fun value good => ihi domain value good) argument returned
          have result := valid argument (bounded_mono inputRow bounded) oldInput
          exact ⟨bounded_mono outputRow result.1,
            allReturns_mono _ _ (fun value good => iho codomain value good) _ result.2⟩
  | record sourceShape _ _ _ _ =>
      exact False.elim (record_has_no_values sourceShape shape value valid)

theorem comp_mono {left right : CoreComp n Key}
    (subtype : Inference.Comp.le (Model n Key) left right)
    {computation : Tree n Key Atom shape} (valid : CompHolds left computation) :
    CompHolds right computation :=
  ⟨bounded_mono subtype.2 valid.1,
    allReturns_mono _ _ (fun value good => subtype_interpretation subtype.1 shape value good)
      computation valid.2⟩

theorem comp_pure (type : CoreComp n Key) (value : Value n Key Atom shape)
    (valid : TypeHolds type.1 shape value) : CompHolds type (.pure value) := ⟨trivial, valid⟩

theorem comp_bind {input output : CoreComp n Key} {computation : Tree n Key Atom a}
    {next : Value n Key Atom a → Tree n Key Atom b}
    (valid : CompHolds input computation)
    (nextValid : ∀ value, TypeHolds input.1 a value → CompHolds output (next value)) :
    CompHolds (output.1, joinRow input.2 output.2) (computation.bind next) :=
  bind_bounds_returns _ _ _ _ _ _ valid.1 valid.2 nextValid

def Environment [DecidableEq Key] (bindings : List (CoreBinding n Key))
    (runtime : Env (Tree n Key Atom) Γ) : Prop :=
  ∀ {shape} (index : OperationalTyping.Var Γ shape) (type : CoreComp n Key),
    RecursiveEffects.BindingLookup (Model n Key) (rowView n Key)
      (signatures n Key) bindings (varIndex index) type → CompHolds type (runtime index)

theorem Environment.nil [DecidableEq Key] :
    Environment ([] : List (CoreBinding n Key)) (Env.nil : Env (Tree n Key Atom) []) :=
  fun index => nomatch index

theorem Environment.cons [DecidableEq Key]
    {bindings : List (CoreBinding n Key)} {runtime : Env (Tree n Key Atom) Γ}
    (environment : Environment bindings runtime)
    (binding : CoreBinding n Key) (value : Tree n Key Atom s)
    (first : ∀ type, CoreBindingTyping binding type → CompHolds type value) :
    Environment (binding :: bindings) (Env.cons value runtime) := by
  intro shape index type lookedUp
  obtain ⟨selected, lookup, typed⟩ := lookedUp
  cases index with
  | here =>
      simp only [varIndex, List.getElem?_cons_zero] at lookup
      cases Option.some.inj lookup
      exact first type typed
  | there index =>
      exact environment index type ⟨selected, lookup, typed⟩

theorem Environment.mono [DecidableEq Key]
    {bindings : List (CoreBinding n Key)} {runtime : Env (Tree n Key Atom) Γ}
    (environment : Environment bindings runtime)
    (type : CoreComp n Key) (value : Tree n Key Atom s) (valid : CompHolds type value) :
    Environment (.mono type :: bindings) (Env.cons value runtime) := by
  apply environment.cons (.mono type) value
  intro target typed
  cases typed with
  | mono subtype => exact comp_mono subtype valid

theorem empty_bound_is_pure (computation : Computation n Key Payload Response A)
    (bound : BoundedBy emptyRow computation) : ∃ value, computation = .pure value := by
  cases computation with
  | pure value => exact ⟨value, rfl⟩
  | request occurrence payload resume => exact False.elim bound.1

theorem comp_pair {leftType rightType : CoreComp n Key}
    {left : Tree n Key Atom a} {right : Tree n Key Atom b}
    (leftValid : CompHolds leftType left) (rightValid : CompHolds rightType right) :
    CompHolds (shape := .pair a b)
      ((.pair leftType.1 rightType.1, joinRow leftType.2 rightType.2) : CoreComp n Key)
      (left.bind fun a => right.bind fun b => .pure (a, b)) := by
  apply comp_bind (output := (.pair leftType.1 rightType.1, rightType.2)) leftValid
  intro a ha
  have paired := comp_bind (output := (.pair leftType.1 rightType.1, emptyRow)) rightValid
    (fun b hb => comp_pure (.pair leftType.1 rightType.1, emptyRow) (show Value n Key Atom (.pair _ _) from (a, b))
      ⟨ha, hb⟩)
  simpa only [join_empty] using paired

theorem comp_fst {leftType rightType : CoreType n Key} {row : SetRow n Key}
    {pair : Tree n Key Atom (.pair a b)}
    (valid : CompHolds ((.pair leftType rightType, row) : CoreComp n Key) pair) :
    CompHolds (leftType, row) (pair.bind fun value => .pure value.1) := by
  have projected := comp_bind (output := (leftType, emptyRow)) valid
    (fun value good => comp_pure (leftType, emptyRow) value.1 good.1)
  simpa only [join_empty] using projected

theorem comp_snd {leftType rightType : CoreType n Key} {row : SetRow n Key}
    {pair : Tree n Key Atom (.pair a b)}
    (valid : CompHolds ((.pair leftType rightType, row) : CoreComp n Key) pair) :
    CompHolds (rightType, row) (pair.bind fun value => .pure value.2) := by
  have projected := comp_bind (output := (rightType, emptyRow)) valid
    (fun value good => comp_pure (rightType, emptyRow) value.2 good.2)
  simpa only [join_empty] using projected

theorem comp_request (key : Key) {row : SetRow n Key} {payload : Tree n Key Atom .atom}
    (valid : CompHolds ((.base .unit, row) : CoreComp n Key) payload) :
    CompHolds (shape := .atom) ((.base .unit, joinRow row ((algebra n Key).head key)) : CoreComp n Key)
      (payload.bind fun value => .request (raw key) value (fun response => .pure response)) := by
  apply comp_bind (output := (.base .unit, ((algebra n Key).head key))) valid
  intro value _
  exact ⟨⟨rfl, fun _ => trivial⟩, fun _ => rfl⟩

theorem comp_resumption (input : CoreComp n Key)
    (resume : Atom → Tree n Key Atom a) (valid : ∀ response, CompHolds input (resume response)) :
    TypeHolds (.arrow (.base .unit) emptyRow input.1 input.2) (.arrow .atom a)
      (fun argument => argument.bind resume) := by
  intro argument bounded returned
  have resumed := comp_bind (input := (.base .unit, emptyRow)) (output := input)
    (computation := argument) ⟨bounded, returned⟩ (fun response _ => valid response)
  simpa only [empty_join, CompHolds] using resumed

theorem comp_mapRequests (boundary : Boundary n Key) {input : CoreComp n Key}
    {computation : Tree n Key Atom s} (valid : CompHolds input computation) :
    CompHolds (input.1, RowInference.Boundary.row (algebra n Key) boundary input.2)
      (Computation.mapRequests boundary.transform computation) := by
  refine ⟨?_, (allReturns_mapRequests _ _ _).mpr valid.2⟩
  cases boundary with
  | protect scope permission => exact (InfiniteRowHygiene.protect_bounded_iff _ _ _ _).mpr valid.1
  | release scope permission => exact (InfiniteRowHygiene.release_bounded_iff _ _ _ _).mpr valid.1

theorem comp_shallowHandle [DecidableEq Key]
    (handled : List Key) (input : CoreComp n Key) (output : CoreType n Key)
    (returnRow operationRow : SetRow n Key)
    (onReturn : Value n Key Atom a → Tree n Key Atom b)
    (onOperation : Occurrence n Key → Atom →
      (Atom → Tree n Key Atom a) → Tree n Key Atom b)
    (returnValid : ∀ value, TypeHolds input.1 a value →
      CompHolds (output, returnRow) (onReturn value))
    (operationValid : ∀ occurrence payload resume, Capturable handled occurrence →
      (∀ response, CompHolds input (resume response)) →
      CompHolds (output, operationRow) (onOperation occurrence payload resume))
    (computation : Tree n Key Atom a) (inputValid : CompHolds input computation) :
    CompHolds (output, joinRow (residualRow handled input.2) (joinRow returnRow operationRow))
      (Computation.shallowHandle handled onReturn onOperation computation) := by
  induction computation with
  | pure value =>
      have good := returnValid value inputValid.2
      exact ⟨bounded_mono
        (fun _ member => Or.inr (Or.inl member)) good.1,
          good.2⟩
  | request occurrence payload resume ih =>
      have resumeValid (response : Atom) : CompHolds input (resume response) :=
        ⟨inputValid.1.2 response, inputValid.2 response⟩
      by_cases captured : Capturable handled occurrence
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        have good := operationValid occurrence payload resume captured resumeValid
        exact ⟨bounded_mono
          (fun _ member => Or.inr (Or.inr member)) good.1,
            good.2⟩
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        refine ⟨⟨?_, fun response => (ih response (resumeValid response)).1⟩,
          fun response => (ih response (resumeValid response)).2⟩
        exact Or.inl ⟨inputValid.1.1, captured⟩

/-- Fundamental theorem for the existing recursive type system, specialized
only by resolved runtime shapes and homogeneous operation signatures. It does
not take an operational action/arm bound or checker correctness as a premise. -/
theorem erasure_typing_sound [DecidableEq Key] (expression : Expr n Key Atom Γ s) :
    ∀ (bindings : List (CoreBinding n Key)) (output : CoreComp n Key),
      CoreTyping bindings (erase expression) output →
      ∀ runtime : Env (Tree n Key Atom) Γ, Environment bindings runtime →
        CompHolds output (eval runtime expression) := by
  induction expression with
  | var index =>
      intro bindings output typed runtime environment
      cases typed with
      | var lookup bindingTyped => exact environment index output ⟨_, lookup, bindingTyped⟩
  | lit value =>
      intro bindings output typed runtime environment
      cases typed with
      | lit subtype =>
          exact comp_mono subtype
            (comp_pure (shape := .atom) ((.base .unit, emptyRow) : CoreComp n Key) value rfl)
  | lam input body ih =>
      intro bindings output typed runtime environment
      cases typed with
      | lam bodyTyped subtype =>
          apply comp_mono subtype
          apply comp_pure
          intro argument bounded returned
          exact ih _ _ bodyTyped _ (environment.mono _ argument ⟨bounded, returned⟩)
  | app function argument ihf iha =>
      intro bindings output typed runtime environment
      cases typed with
      | app functionTyped argumentTyped subtype =>
          apply comp_mono subtype
          apply comp_bind (ihf _ _ functionTyped runtime environment)
          intro function functionValid
          have argumentValid := iha _ _ argumentTyped runtime environment
          exact functionValid _ argumentValid.1 argumentValid.2
  | pair left right ihl ihr =>
      intro bindings output typed runtime environment
      cases typed with
      | pair leftTyped rightTyped subtype =>
          exact comp_mono subtype (comp_pair (ihl _ _ leftTyped runtime environment)
            (ihr _ _ rightTyped runtime environment))
  | fst pair ih =>
      intro bindings output typed runtime environment
      cases typed with
      | fst pairTyped subtype => exact comp_mono subtype (comp_fst (ih _ _ pairTyped runtime environment))
  | snd pair ih =>
      intro bindings output typed runtime environment
      cases typed with
      | snd pairTyped subtype => exact comp_mono subtype (comp_snd (ih _ _ pairTyped runtime environment))
  | letE value body ihv ihb =>
      intro bindings output typed runtime environment
      cases typed with
      | letComputed valueTyped bodyTyped subtype =>
          apply comp_mono subtype
          apply comp_bind (ihv _ _ valueTyped runtime environment)
          intro value valueValid
          exact ihb _ _ bodyTyped _
            (environment.mono (Inference.Comp.pure (Model n Key) _) (.pure value)
              (comp_pure (Inference.Comp.pure (Model n Key) _) value valueValid))
      | letValue nonexpansive valueTyped bodyTyped =>
          have valueValid := ihv _ _ valueTyped runtime environment
          obtain ⟨value, evaluation⟩ := empty_bound_is_pure _ valueValid.1
          simp only [eval, evaluation, Computation.bind]
          apply ihb _ _ bodyTyped
          apply environment.cons _ (.pure value)
          intro type bindingTyped
          cases bindingTyped with
          | poly instanceTyped emptyRow =>
              have instanceValid := ihv _ _ instanceTyped runtime environment
              rw [evaluation] at instanceValid
              exact comp_pure type value instanceValid.2
  | request key payload ih =>
      intro bindings output typed runtime environment
      cases typed with
      | request payloadTyped subtype rowBound =>
          rename_i er
          change SetRow n Key at er
          refine comp_mono (left := (.base .unit, joinRow er ((algebra n Key).head key)))
            ⟨subtype, ?_⟩ ?_
          · change Included (joinRow er ((algebra n Key).head key)) output.2
            change Included (joinRow er (joinRow ((algebra n Key).head key) emptyRow)) output.2 at rowBound
            intro occurrence member
            exact rowBound occurrence (member.elim Or.inl (fun head => Or.inr (Or.inl head)))
          · exact comp_request key (ih _ _ payloadTyped runtime environment)
  | boundary boundary body ih =>
      intro bindings output typed runtime environment
      cases typed with
      | boundary bodyTyped subtype rowBound =>
          rename_i input
          change CoreComp n Key at input
          refine comp_mono (left := (input.1, RowInference.Boundary.row (algebra n Key) boundary input.2))
            ⟨subtype, ?_⟩ ?_
          · cases boundary <;> exact rowBound
          · exact comp_mapRequests boundary (ih _ _ bodyTyped runtime environment)
  | handler key target action onReturn onOperation iha ihr iho =>
      intro bindings output typed runtime environment
      cases typed with
      | handler actionTyped returnTyped operationTyped resultSubtype rowBound =>
          rename_i input returned operated
          refine comp_mono (left := (.union returned.1 operated.1,
            joinRow (residualRow [key] input.2) (joinRow returned.2 operated.2)))
            ⟨resultSubtype, ?_⟩ ?_
          · exact rowBound
          · apply comp_shallowHandle
            · intro value valueValid
              have returned := ihr _ _ returnTyped _
                (environment.mono (input.1, emptyRow) (.pure value) (comp_pure (input.1, emptyRow) value valueValid))
              exact ⟨returned.1,
                allReturns_mono _ _ (fun _ good => Or.inl good) _ returned.2⟩
            · intro occurrence payload resume captured resumeGood
              have continuation := comp_pure (shape := .arrow .atom _)
                ((.arrow (.base .unit) emptyRow input.1 input.2, emptyRow) : CoreComp n Key)
                (fun argument => argument.bind resume) (comp_resumption _ resume resumeGood)
              have payloadValid := comp_pure ((.base .unit, emptyRow) : CoreComp n Key)
                (shape := .atom) payload rfl
              have operated := iho _ _ operationTyped _
                (Environment.mono (Environment.mono environment _ _ continuation) _ _ payloadValid)
              exact ⟨operated.1,
                allReturns_mono _ _ (fun _ good => Or.inr good) _ operated.2⟩
            · exact iha _ _ actionTyped runtime environment
  | widen target body ih =>
      intro bindings output typed runtime environment
      exact ih bindings output typed runtime environment

/-- A solution of the existing generator's formula supplies the complete
operational interpretation at a possibly infinite output row. This theorem
uses neither the resolved finite-row checker nor an operational bound premise. -/
theorem principal_operationally_valid [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CoreComp n Key)
    (solution : (principal expression).Holds (Model n Key) (rowView n Key)
      (Inference.extend Empty.elim output)) :
    CompHolds output (eval Env.nil expression) := by
  have typed := (RecursiveEffects.principal_exact (Model n Key) (rowView n Key)
    (signatures n Key) (erase expression) (signatureTerms Key Empty) [] [] Empty.elim
    (RecursiveEffects.EnvRel.nil _ _ _ _) (fun _ => rfl) output).mp solution
  exact erasure_typing_sound expression [] output typed Env.nil Environment.nil

theorem principal_effect_bound [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CoreComp n Key)
    (solution : (principal expression).Holds (Model n Key) (rowView n Key)
      (Inference.extend Empty.elim output)) :
    BoundedBy output.2 (eval Env.nil expression) :=
  (principal_operationally_valid expression output solution).1

/-- The same generated solution bounds the same evaluated expression after
fresh allocation and proves that a default boundary cannot be captured.
Values are unchanged by this explicit immediate-request transformation;
latent-value wrappers and source boundary allocation are separate obligations. -/
theorem principal_fresh_boundary [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CoreComp n Key)
    (solution : (principal expression).Holds (Model n Key) (rowView n Key)
      (Inference.extend Empty.elim output))
    (handled : List Key)
    (onReturn : Value n Key Atom s → Computation (n + 1) Key Atom Atom Result)
    (onOperation : Occurrence (n + 1) Key → Atom →
      (Atom → Computation (n + 1) Key Atom Atom (Value n Key Atom s)) →
        Computation (n + 1) Key Atom Atom Result) :
    BoundedBy
      (InfiniteRowHygiene.protectRow FreshBoundaries.fresh allowNone
        (InfiniteRowHygiene.liftRow output.2))
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree (eval Env.nil expression))) ∧
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree (eval Env.nil expression))) =
      (Computation.mapRequests (Directed.protect FreshBoundaries.fresh allowNone)
        (FreshBoundaries.liftTree (eval Env.nil expression))).bind onReturn :=
  InfiniteRowHygiene.fresh_boundary output.2 (eval Env.nil expression)
    (principal_effect_bound expression output solution) handled onReturn onOperation

end Yulang.InfiniteOperationalCorrespondence
