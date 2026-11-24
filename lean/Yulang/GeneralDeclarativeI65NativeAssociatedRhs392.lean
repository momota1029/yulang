import Yulang.GeneralDeclarativeI65AddressedReplay390
import Yulang.GeneralDeclarativeAssocRule323
import Yulang.GeneralDeclarativeI65Capture366

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarationPatterns (Pattern normalize)
open CommonDeclaredNominalInspection (Parameter)
open CommonDeclaredNominalVariance (Variance)
open CommonRecursiveNominalIntervals
  (Endpoint Argument childContext effectiveParameter ContextWellFormed
    ContextArgumentsWellFormed ContextArgumentWellFormed)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- A real read, never an out-of-range fallback. Explicit body names look
up the independently selected event. Role default names use positional
inputs and the existing C320 default actual-center convention. -/
def writtenBodySlot392 {s : State} {q : Request} (event : LiteralLocalEvent s q) (body : Body)
    (binder : Nat) : Option Capture :=
  match body with
  | .explicit _ => event.captures.lookup binder
  | .default _ _ _ => (q.demand.arguments[binder]?).map fun c => ⟨c.center,c.center,c.center⟩

/-- An actual model-free typed source binding for each use. Numeric
slot identity is not a value/row coercion. The present C386 carrier
does not by itself supply these witnesses from the selected head. -/
inductive TypedBodyCapture392 (s : State) (c : Capture) :
    CommonDeclaredNominalInspection.Kind → Prop where
  | value {lo hi} : ValueBind s c lo hi → TypedBodyCapture392 s c .value
  | row {lo hi} : RowBind s c lo hi → TypedBodyCapture392 s c .row

mutual
/-- Source-local native application rule. A full catalogue Use must match
the current declared variance table at every position. Neither model
values, output receipts, solver allocations nor release enter. -/
inductive NativeBodyRhs392 (s : State) (slots : Nat → Option Capture) :
    Bool → Pattern → Endpoint Nat → Prop where
  | binder {context binder c} :
      slots binder = some c → TypedBodyCapture392 s c .value → NativeBodyRhs392 s slots context (.var binder) (.ordinary (.var c.center))
  | app {context ctor pats args params} (use : Use s.current.environment ctor pats.length) :
      names use.mode pats.length = some params →
      s.modes[ctor]? = some params →
      NativeBodyArgs392 s slots context params pats args →
      NativeBodyRhs392 s slots context (.app ctor pats) (.nominal ctor args)

inductive NativeBodyArgs392 (s : State) (slots : Nat → Option Capture) :
    Bool → List Parameter → List Pattern → List (Argument Nat) → Prop where
  | nil : NativeBodyArgs392 s slots context [] [] []
  | cons :
      NativeBodyArg392 s slots context param p arg →
      NativeBodyArgs392 s slots context ps pats args →
      NativeBodyArgs392 s slots context (param :: ps) (p :: pats) (arg :: args)

inductive NativeBodyArg392 (s : State) (slots : Nat → Option Capture) :
    Bool → Parameter → Pattern → Argument Nat → Prop where
  | pointValue {p binder c} :
      p.kind = .value → (effectiveParameter context p).variance ≠ .invariant →
      slots binder = some c → TypedBodyCapture392 s c .value →
      NativeBodyArg392 s slots context p (.var binder) (.inl (.point (.ordinary (.var c.center))))
  | intervalValue {p binder c} :
      p.kind = .value → (effectiveParameter context p).variance = .invariant →
      slots binder = some c → TypedBodyCapture392 s c .value →
      NativeBodyArg392 s slots context p (.var binder)
        (.inl (.interval (.ordinary (.var c.lower)) (.ordinary (.var c.upper))))
  | pointRow {p binder c} :
      p.kind = .row → (effectiveParameter context p).variance ≠ .invariant →
      slots binder = some c → TypedBodyCapture392 s c .row →
      NativeBodyArg392 s slots context p (.var binder) (.inr (.point (.var c.center)))
  | intervalRow {p binder c} :
      p.kind = .row → (effectiveParameter context p).variance = .invariant →
      slots binder = some c → TypedBodyCapture392 s c .row →
      NativeBodyArg392 s slots context p (.var binder) (.inr (.interval (.var c.lower) (.var c.upper)))
  | nominal {p ctor pats endpoint} :
      p.kind = .value →
      NativeBodyRhs392 s slots (childContext context p) (.app ctor pats) endpoint →
      NativeBodyArg392 s slots context p (.app ctor pats) (.inl (.point endpoint))
end

private theorem effective_kind_value392 (context : Bool) (p : Parameter) (kind : p.kind = .value) :
    (effectiveParameter context p).kind = .value := kind

private theorem effective_kind_row392 (context : Bool) (p : Parameter) (kind : p.kind = .row) :
    (effectiveParameter context p).kind = .row := kind

private theorem parameter_of_fields392 {p : Parameter} {kind variance}
    (hk : p.kind = kind) (hv : p.variance = variance) : p = ⟨kind,variance⟩ := by
  cases p
  simp_all

theorem native_rhs_wellformed392 {s : State} {slots : Nat → Option Capture}
    {context p endpoint} (made : NativeBodyRhs392 s slots context p endpoint) :
    ContextWellFormed s.modes context endpoint := by
  exact NativeBodyRhs392.rec
    (motive_1 := fun c _ t _ => ContextWellFormed s.modes c t)
    (motive_2 := fun c ps _ as _ => ContextArgumentsWellFormed s.modes c ps as)
    (motive_3 := fun c p _ a _ =>
      ContextArgumentWellFormed s.modes (childContext c p) (effectiveParameter c p) a)
    (fun _ _ => .ordinary _ _)
    (fun _ _ found _ beyond => .nominal found beyond)
    (fun {c} => .nil c)
    (fun _ _ first rest => .cons first rest)
    (fun {c p _ _} hk _ _ _ => by
      rw [parameter_of_fields392 (effective_kind_value392 c p hk) rfl]
      exact .valuePoint (.ordinary _ _))
    (fun {c p _ _} hk hv _ _ => by
      rw [parameter_of_fields392 (effective_kind_value392 c p hk) hv]
      exact .valueInterval (.ordinary _ _) (.ordinary _ _))
    (fun {c p _ _} hk _ _ _ => by
      rw [parameter_of_fields392 (effective_kind_row392 c p hk) rfl]
      exact .rowPoint _ _ _)
    (fun {c p _ _} hk hv _ _ => by
      rw [parameter_of_fields392 (effective_kind_row392 c p hk) hv]
      exact .rowInterval _ _ _)
    (fun {c p _ _ _} hk _ nested => by
      rw [parameter_of_fields392 (effective_kind_value392 c p hk) rfl]
      exact .valuePoint nested)
    made

/-- A represented source tree determines its vector in order. Two
different derivations cannot pick different captures or kind tables. -/
theorem native_body_rhs_functional392 {s : State} {slots : Nat → Option Capture}
    {context p first} (built : NativeBodyRhs392 s slots context p first) :
    ∀ second, NativeBodyRhs392 s slots context p second → first = second := by
  exact NativeBodyRhs392.rec
    (motive_1 := fun c p a _ => ∀ b, NativeBodyRhs392 s slots c p b → a = b)
    (motive_2 := fun c ps pts as _ => ∀ bs, NativeBodyArgs392 s slots c ps pts bs → as = bs)
    (motive_3 := fun c p pt a _ => ∀ b, NativeBodyArg392 s slots c p pt b → a = b)
    (fun firstSlot _ _ alternative => by
      cases alternative with
      | binder secondSlot _ =>
        cases Option.some.inj (firstSlot.symm.trans secondSlot)
        rfl)
    (fun _ _ firstTable _ argsSound _ alternative => by
      cases alternative with
      | app _ _ secondTable args =>
        cases Option.some.inj (firstTable.symm.trans secondTable)
        exact congrArg (Endpoint.nominal _) (argsSound _ args))
    (fun _ alternative => by cases alternative; rfl)
    (fun _ _ firstArg tailArgs _ alternative => by
      cases alternative with
      | cons head tail =>
        rw [firstArg _ head,tailArgs _ tail])
    (fun firstKind firstMode firstSlot _ _ alternative => by
      cases alternative <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ alternative => by
      cases alternative <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ alternative => by
      cases alternative <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ alternative => by
      cases alternative <;> simp_all)
    (fun _ _ nested _ alternative => by
      cases alternative with
      | nominal _ inner => rw [nested _ inner])
    built

/-- Lower the selected associated body, not a code supplied by the receipt.
The two represented native forms are bare and same-root tagged apps.
Original normalized syntax is retained, including the tag, and the
general arity/mixed vector is computed by the derivation. -/
inductive NativeAssociatedRhs392 {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (body : Body) (target : Nat) : LiteralWriteSyntax → Prop where
  | direct {ctor pats args} :
      normalize (bodyPattern body) = .app ctor pats →
      NativeBodyRhs392 s (writtenBodySlot392 event body) false (.app ctor pats) (.nominal ctor args) →
      NativeAssociatedRhs392 event body target (.declared target (.app ctor pats) args)
  | tagged {tag ctor pats args} :
      normalize (bodyPattern body) = .variant tag (.app ctor pats) →
      NativeBodyRhs392 s (writtenBodySlot392 event body) false (.app ctor pats) (.nominal ctor args) →
      NativeAssociatedRhs392 event body target (.declared target (.variant tag (.app ctor pats)) args)

theorem native_associated_rhs_functional392
    {s : State} {q : Request} {event : LiteralLocalEvent s q} {body target first second}
    (left : NativeAssociatedRhs392 event body target first)
    (right : NativeAssociatedRhs392 event body target second) : first = second := by
  cases left with
  | direct source evaluated =>
    cases right with
    | direct source' evaluated' =>
      have matchSource := source.symm.trans source'
      cases Pattern.app.inj matchSource with
      | intro sameCtor samePats =>
        cases sameCtor
        cases samePats
        have matchPayload := native_body_rhs_functional392 evaluated _ evaluated'
        exact congrArg _ (Endpoint.nominal.inj matchPayload).2
    | tagged other _ => cases source.symm.trans other
  | tagged source evaluated =>
    cases right with
    | direct other _ => cases source.symm.trans other
    | tagged source' evaluated' =>
      have matchSource := source.symm.trans source'
      obtain ⟨sameTag,matched⟩ := Pattern.variant.inj matchSource
      obtain ⟨sameCtor,samePats⟩ := Pattern.app.inj matched
      cases sameTag
      cases sameCtor
      cases samePats
      have matchPayload := native_body_rhs_functional392 evaluated _ evaluated'
      exact congrArg _ (Endpoint.nominal.inj matchPayload).2

/-- A concrete local output rule at the original ordinal. Production
is independent of the receipt and independent of candidate selection. -/
structure ModelFreeNativeOutputAt392 {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (ordinal : Nat) (out : GeneralSourceState.Output) (body : Body) (written : LiteralWriteSyntax) : Prop where
  ordinalExact : q.demand.outputs[ordinal]? = some out
  supplier : Supplies (authoredRegistry s.current).roles event.declaration out.name body
  derived : NativeAssociatedRhs392 event body out.target written

theorem native_associated_rhs_writes_exact_target392
    {s : State} {q : Request} {event : LiteralLocalEvent s q} {body target written}
    (derived : NativeAssociatedRhs392 event body target written) :
    ∃ sourcePattern arguments, written = .declared target sourcePattern arguments := by
  cases derived <;> exact ⟨_,_,rfl⟩

/-- The concrete local rule produces its literal receipt directly.
No equality with supplied receipt data is needed to produce it. -/
def emitNativeOutput392 (q : Request) (i : Nat) (out : GeneralSourceState.Output)
    (body : Body) (written : LiteralWriteSyntax) : OrderedReceipt :=
  ⟨q.occurrence,i,out,body,written⟩

theorem native_source_emits_original_receipt392
    {s : State} {q : Request} {event : LiteralLocalEvent s q} {i out body written}
    (made : ModelFreeNativeOutputAt392 event i out body written) :
    let receipt := emitNativeOutput392 q i out body written
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
      q.demand.outputs[i]? = some receipt.requested ∧
      Supplies (authoredRegistry s.current).roles event.declaration receipt.requested.name receipt.source ∧
      receipt.writesTarget ∧
      NativeAssociatedRhs392 event receipt.source receipt.requested.target receipt.written := by
  obtain ⟨_,_,fixed⟩ := native_associated_rhs_writes_exact_target392 made.derived
  exact ⟨rfl,rfl,made.ordinalExact,made.supplier,by
    simp only [emitNativeOutput392,OrderedReceipt.writesTarget,fixed],made.derived⟩

theorem original_body_has_literal_position392 {s : State} {q : Request}
    {event : LiteralLocalEvent s q} {i out body written}
    (made : ModelFreeNativeOutputAt392 event i out body written)
    {receipt : OrderedReceipt} (atIndex : event.receipts[i]? = some receipt)
    (sameSupplier : receipt.source = body) (choice : receipt.written = written) :
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
    receipt.requested = out ∧
    NativeAssociatedRhs392 event receipt.source receipt.requested.target receipt.written := by
  obtain ⟨path, ordinal, requested, _, _⟩ := event.receiptAt i receipt atIndex
  have request : receipt.requested = out := Option.some.inj (requested.symm.trans made.ordinalExact)
  exact ⟨path,ordinal,request,by simpa only [sameSupplier,choice,request] using made.derived⟩

end Yulang.GeneralDeclarativeI65
