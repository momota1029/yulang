import Yulang.OperationalTransport
import Yulang.InfiniteOperationalCorrespondence

/-!
# Higher-order operational transport at arbitrary inferred rows

The wrappers in `OperationalTransport` act on the same computation-argument
functions and request trees used by the resolved evaluator. This module maps
the rows of the existing structural types and proves that the wrappers preserve
and reflect their operational interpretation, including latent functions in
pairs, unions and intersections. Rows are arbitrary occurrence predicates;
neither finite support nor a bound on signed weights is assumed.

The static type maps all of its rows in the same direction. At an arrow the
runtime wrapper converts its argument back in the opposite direction before
calling the original function. No source boundary insertion policy is chosen,
and the existing immediate-only `Expr.boundary` is unchanged.
-/

namespace Yulang.InfiniteOperationalTransport

open Directed OperationalTyping
open RecursiveRows (SetRow)
open InfiniteRowHygiene (Included image BoundedBy)
open InfiniteOperationalCorrespondence (CoreType CoreComp TypeHolds CompHolds)
open OperationalTransport (Direction request value tree)

/-- The image under the same signed request bijection used at runtime. -/
def row (scope : Fin n) (permission : Permission Key) (direction : Direction)
    (original : SetRow n Key) : SetRow n Key :=
  image (request scope permission direction) original

theorem request_injective (scope : Fin n) (permission : Permission Key)
    (direction : Direction) : Function.Injective (request scope permission direction) := by
  intro left right same
  have restored := congrArg (request scope permission direction.opposite) same
  simpa only [request, DirectedHigherOrder.requestTransport_opposite] using restored

@[simp] theorem row_opposite (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : SetRow n Key) :
    row scope permission direction.opposite (row scope permission direction original) = original :=
  InfiniteRowHygiene.image_inverse _ _
    (DirectedHigherOrder.requestTransport_opposite scope permission direction) original

theorem row_included_iff (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (left right : SetRow n Key) :
    Included (row scope permission direction left) (row scope permission direction right) ↔
      Included left right :=
  InfiniteRowHygiene.image_included_iff _ (request_injective scope permission direction) left right

/-- Static arrow inputs have the same transformed interface as outputs. The
opposite direction occurs in the runtime argument wrapper, not in this type. -/
def type (scope : Fin n) (permission : Permission Key) (direction : Direction) :
    CoreType n Key → CoreType n Key
  | .base base => .base base
  | .bottom => .bottom
  | .union left right => .union (type scope permission direction left) (type scope permission direction right)
  | .inter left right => .inter (type scope permission direction left) (type scope permission direction right)
  | .pair left right => .pair (type scope permission direction left) (type scope permission direction right)
  | .emptyRecord => .emptyRecord
  | .record label field rest => .record label (type scope permission direction field)
      (type scope permission direction rest)
  | .variant label payload => .variant label (type scope permission direction payload)
  | .arrow input inputRow output outputRow =>
      .arrow (type scope permission direction input) (row scope permission direction inputRow)
        (type scope permission direction output) (row scope permission direction outputRow)

def comp (scope : Fin n) (permission : Permission Key) (direction : Direction)
    (original : CoreComp n Key) : CoreComp n Key :=
  (type scope permission direction original.1, row scope permission direction original.2)

@[simp] theorem type_opposite (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : CoreType n Key) :
    type scope permission direction.opposite (type scope permission direction original) = original := by
  induction original <;> simp_all [type]

@[simp] theorem comp_opposite (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : CoreComp n Key) :
    comp scope permission direction.opposite (comp scope permission direction original) = original := by
  simp [comp]

theorem mapBoth_bound_iff (transform : Occurrence n Key → Occurrence n Key)
    (injective : Function.Injective transform) (onValue : A → B) (original : SetRow n Key)
    (computation : Computation n Key Payload Response A) :
    BoundedBy (image transform original) (DirectedHigherOrder.mapBoth transform onValue computation) ↔
      BoundedBy original computation := by
  induction computation with
  | pure v => rfl
  | request occurrence payload resume ih =>
      simp only [DirectedHigherOrder.mapBoth, BoundedBy, Computation.AllRequests,
        InfiniteRowHygiene.image_apply_iff transform injective, ih]

theorem mapBoth_returns_iff (transform : Occurrence n Key → Occurrence n Key)
    (onValue : A → B) (before : A → Prop) (after : B → Prop)
    (same : ∀ v, after (onValue v) ↔ before v)
    (computation : Computation n Key Payload Response A) :
    AllReturns after (DirectedHigherOrder.mapBoth transform onValue computation) ↔
      AllReturns before computation := by
  induction computation with
  | pure v => exact same v
  | request occurrence payload resume ih =>
      simp only [DirectedHigherOrder.mapBoth, AllReturns, ih]

theorem tree_bound_iff (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : SetRow n Key) (computation : Tree n Key Atom shape) :
    BoundedBy (row scope permission direction original)
      (tree scope permission shape direction computation) ↔ BoundedBy original computation :=
  mapBoth_bound_iff _ (request_injective scope permission direction) _ original computation

private theorem tree_comp_iff_of_value (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : CoreComp n Key) (shape : Shape)
    (same : ∀ v : Value n Key Atom shape,
      TypeHolds (type scope permission direction original.1) shape
        (value scope permission shape direction v) ↔ TypeHolds original.1 shape v)
    (computation : Tree n Key Atom shape) :
    CompHolds (comp scope permission direction original)
      (tree scope permission shape direction computation) ↔ CompHolds original computation := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr (tree_bound_iff scope permission direction original.2 computation)
    (mapBoth_returns_iff _ _ _ _ same computation)

/-- This is an equivalence for every value, including arbitrary functions of
suspended computations. A runtime effect-bound assumption is not added. -/
theorem typeHolds_iff (scope : Fin n) (permission : Permission Key) (original : CoreType n Key) :
    ∀ (direction : Direction) (shape : Shape) (v : Value n Key Atom shape),
      TypeHolds (type scope permission direction original) shape
        (value scope permission shape direction v) ↔ TypeHolds original shape v := by
  induction original with
  | base base => intro direction shape v; cases shape <;> rfl
  | bottom => intro direction shape v; rfl
  | union left right ihl ihr =>
      intro direction shape v
      exact or_congr (ihl direction shape v) (ihr direction shape v)
  | inter left right ihl ihr =>
      intro direction shape v
      exact and_congr (ihl direction shape v) (ihr direction shape v)
  | pair left right ihl ihr =>
      intro direction shape v
      cases shape with
      | atom => rfl
      | arrow a b => rfl
      | pair a b => exact and_congr (ihl direction a v.1) (ihr direction b v.2)
  | emptyRecord => intro direction shape v; rfl
  | record => intro direction shape v; rfl
  | variant => intro direction shape v; rfl
  | arrow input inputRow output outputRow ihi iho =>
      intro direction shape f
      cases shape with
      | atom => rfl
      | pair a b => rfl
      | arrow domain codomain =>
          have inputIff := tree_comp_iff_of_value (Atom := Atom) scope permission direction
            (input, inputRow) domain (ihi direction domain)
          have outputIff := tree_comp_iff_of_value (Atom := Atom) scope permission direction
            (output, outputRow) codomain (iho direction codomain)
          constructor
          · intro transformed argument bounded returned
            have validArgument := (inputIff argument).mpr ⟨bounded, returned⟩
            have result := transformed (tree scope permission domain direction argument)
              validArgument.1 validArgument.2
            apply (outputIff (f argument)).mp
            change CompHolds (comp scope permission direction (output, outputRow))
              (value scope permission (.arrow domain codomain) direction f
                (tree scope permission domain direction argument)) at result
            rw [OperationalTransport.value_apply_tree] at result
            exact result
          · intro originalValid argument bounded returned
            have validArgument : CompHolds (input, inputRow)
                (tree scope permission domain direction.opposite argument) := by
              apply (inputIff _).mp
              have cancel := OperationalTransport.tree_opposite scope permission domain
                direction.opposite argument
              simp only [HigherOrder.Direction.opposite_opposite] at cancel
              rw [cancel]
              exact ⟨bounded, returned⟩
            exact (outputIff _).mpr (originalValid _ validArgument.1 validArgument.2)

/-- Exact operational meaning is preserved for immediate and latent rows. -/
theorem compHolds_iff (scope : Fin n) (permission : Permission Key) (direction : Direction)
    (original : CoreComp n Key) (computation : Tree n Key Atom shape) :
    CompHolds (comp scope permission direction original)
      (tree scope permission shape direction computation) ↔ CompHolds original computation :=
  tree_comp_iff_of_value scope permission direction original shape
    (typeHolds_iff scope permission original.1 direction shape) computation

/-- The same principal-formula solution now certifies wrappers inside returned
closures as well as the immediate request tree, at finite or infinite rows. -/
theorem principal_transport_valid [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CoreComp n Key)
    (solution : (OperationalCorrespondence.principal expression).Holds
      (InfiniteOperationalCorrespondence.Model n Key)
      (InfiniteOperationalCorrespondence.rowView n Key) (Inference.extend Empty.elim output))
    (scope : Fin n) (permission : Permission Key) (direction : Direction) :
    CompHolds (comp scope permission direction output)
      (tree scope permission shape direction (eval Env.nil expression)) :=
  (compHolds_iff scope permission direction output (eval Env.nil expression)).mpr
    (InfiniteOperationalCorrespondence.principal_operationally_valid expression output solution)

/-- A suitably typed argument can be converted back before entering the
original function. Its immediate effects need not be empty. -/
theorem call_valid (scope : Fin n) (permission : Permission Key) (direction : Direction)
    (input output : CoreComp n Key) (function : Value n Key Atom (.arrow domain codomain))
    (typed : TypeHolds (.arrow input.1 input.2 output.1 output.2)
      (.arrow domain codomain) function)
    (argument : Tree n Key Atom domain)
    (argumentValid : CompHolds (comp scope permission direction input) argument) :
    CompHolds (comp scope permission direction output)
      (value scope permission (.arrow domain codomain) direction function argument) := by
  have transformed := (typeHolds_iff scope permission
    (.arrow input.1 input.2 output.1 output.2) direction (.arrow domain codomain) function).mpr typed
  exact transformed argument argumentValid.1 argumentValid.2

/-- Static zero origin of the declared output row is enough for noncapture of
a guarded higher-order call. The runtime origin and effect bound are derived
from typing; they are not additional assumptions on the function's execution.
Negative input debts remain allowed and are transported in the opposite
direction. Dropping the output-row condition would incorrectly hide callbacks
whose debt is meant to cancel when they return to their owner. -/
theorem guarded_call_noncapture [DecidableEq Key]
    (scope : Fin n) (input output : CoreComp n Key)
    (function : Value n Key Atom (.arrow domain codomain))
    (typed : TypeHolds (.arrow input.1 input.2 output.1 output.2)
      (.arrow domain codomain) function)
    (argument : Tree n Key Atom domain)
    (argumentValid : CompHolds (comp scope allowNone .guard input) argument)
    (origin : InfiniteRowHygiene.ZeroAt scope output.2)
    (handled : List Key)
    (onReturn : Value n Key Atom codomain → Computation n Key Atom Atom Result)
    (onOperation : Occurrence n Key → Atom →
      (Atom → Tree n Key Atom codomain) → Computation n Key Atom Atom Result) :
    Computation.shallowHandle handled onReturn onOperation
      (value scope allowNone (.arrow domain codomain) .guard function argument) =
      (value scope allowNone (.arrow domain codomain) .guard function argument).bind onReturn := by
  have restored : CompHolds input (tree scope allowNone domain .release argument) := by
    apply (compHolds_iff scope allowNone .guard input _).mp
    have cancel := OperationalTransport.tree_opposite scope allowNone domain .release argument
    simp only [HigherOrder.Direction.opposite] at cancel
    rw [cancel]
    exact argumentValid
  have bounded := (typed _ restored.1 restored.2).1
  have runtimeOrigin := InfiniteRowHygiene.bounded_zeroAt scope output.2 origin
    (function (tree scope allowNone domain .release argument)) bounded
  exact DirectedHigherOrder.guarded_map_noncapture scope
    (value scope allowNone codomain .guard)
    (function (tree scope allowNone domain .release argument)) runtimeOrigin
    handled onReturn onOperation

/-- Freshly reindexed output rows supply the static origin condition even
when the row is infinite and old coordinates contain negative debts. -/
theorem fresh_output_call_noncapture [DecidableEq Key]
    (input : CoreComp (n + 1) Key) (outputType : CoreType (n + 1) Key)
    (oldOutputRow : SetRow n Key)
    (function : Value (n + 1) Key Atom (.arrow domain codomain))
    (typed : TypeHolds
      (.arrow input.1 input.2 outputType (InfiniteRowHygiene.liftRow oldOutputRow))
      (.arrow domain codomain) function)
    (argument : Tree (n + 1) Key Atom domain)
    (argumentValid : CompHolds (comp FreshBoundaries.fresh allowNone .guard input) argument)
    (handled : List Key)
    (onReturn : Value (n + 1) Key Atom codomain → Computation (n + 1) Key Atom Atom Result)
    (onOperation : Occurrence (n + 1) Key → Atom →
      (Atom → Tree (n + 1) Key Atom codomain) → Computation (n + 1) Key Atom Atom Result) :
    Computation.shallowHandle handled onReturn onOperation
      (value FreshBoundaries.fresh allowNone (.arrow domain codomain) .guard function argument) =
      (value FreshBoundaries.fresh allowNone (.arrow domain codomain) .guard function argument).bind
        onReturn :=
  guarded_call_noncapture FreshBoundaries.fresh input
    (outputType, InfiniteRowHygiene.liftRow oldOutputRow) function typed argument argumentValid
    (InfiniteRowHygiene.liftRow_zero oldOutputRow) handled onReturn onOperation

/-- Every eventual closure returned by the transformed evaluation has a sound
call interface and the static-row noncapture guarantee. The only program
premise is a solution of the existing principal constraints; handler arm
bounds, checker acceptance and a runtime-origin witness are not assumed. -/
theorem principal_guarded_arrow_calls [DecidableEq Key]
    (expression : Expr n Key Atom [] (.arrow domain codomain))
    (input output : CoreComp n Key) (evaluationRow : SetRow n Key)
    (solution : (OperationalCorrespondence.principal expression).Holds
      (InfiniteOperationalCorrespondence.Model n Key)
      (InfiniteOperationalCorrespondence.rowView n Key)
      (Inference.extend Empty.elim
        (.arrow input.1 input.2 output.1 output.2, evaluationRow)))
    (scope : Fin n) (origin : InfiniteRowHygiene.ZeroAt scope output.2)
    (handled : List Key)
    (onReturn : Value n Key Atom codomain → Computation n Key Atom Atom Result)
    (onOperation : Occurrence n Key → Atom →
      (Atom → Tree n Key Atom codomain) → Computation n Key Atom Atom Result) :
    AllReturns
      (fun function => ∀ argument, CompHolds (comp scope allowNone .guard input) argument →
        CompHolds (comp scope allowNone .guard output) (function argument) ∧
        Computation.shallowHandle handled onReturn onOperation (function argument) =
          (function argument).bind onReturn)
      (tree scope allowNone (.arrow domain codomain) .guard (eval Env.nil expression)) := by
  apply (OperationalTransport.allReturns_mapBoth _ _ _ _).mpr
  have original := InfiniteOperationalCorrespondence.principal_operationally_valid expression
    (.arrow input.1 input.2 output.1 output.2, evaluationRow) solution
  apply allReturns_mono _ _ _ _ original.2
  intro function typed argument argumentValid
  exact ⟨call_valid scope allowNone .guard input output function typed argument argumentValid,
    guarded_call_noncapture scope input output function typed argument argumentValid origin
      handled onReturn onOperation⟩

end Yulang.InfiniteOperationalTransport
