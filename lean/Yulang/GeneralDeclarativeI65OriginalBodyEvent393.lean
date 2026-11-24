import Yulang.GeneralDeclarativeI65NativeAssociatedRhs392

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeSourceEmission322 (Names demand)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRecursiveNominalIntervals (Argument)

/-- Input from an independently selected original declaration. The
names are generated from the original head/where scopes, rather than
decoded from a prebuilt literal event or a model. -/
structure AuthoredBodyFrame393 (s : State) (q : Request) where
  ordinal : Nat
  decl : Declaration
  authored : (authoredRegistry s.current).declarations[ordinal]? = some decl
  inScope : decl ∈ visible s q
  placement : Placement
  input : Nat → Capture

def AuthoredBodyFrame393.names {s q} (f : AuthoredBodyFrame393 s q) : Names :=
  GeneralDeclarativeFrameReadback325.sourceNames f.decl f.placement f.input

def AuthoredBodyFrame393.whereFor {s q} (f : AuthoredBodyFrame393 s q)
    (clause : GeneralDeclarations.Clause) : LiteralWhereEntry :=
  ⟨clause,demand f.decl clause f.names (f.placement.compound clause) (f.placement.targets clause)⟩

def AuthoredBodyFrame393.clauses {s q} (f : AuthoredBodyFrame393 s q) : List LiteralWhereEntry :=
  f.decl.requirements.map f.whereFor

def AuthoredBodyFrame393.captures {s q} (f : AuthoredBodyFrame393 s q) : List (Nat × Capture) :=
  (f.decl.inputNames ++ f.decl.outputNames).map fun n => (n,f.names.input n)

/-- This reads the generated lexical source, not a list of emitted
outputs. Defaults never read a guessed missing role argument. -/
def AuthoredBodyFrame393.slots {s q} (f : AuthoredBodyFrame393 s q) (body : Body)
    (binder : Nat) : Option Capture :=
  match body with
  | .explicit _ => f.captures.lookup binder
  | .default _ _ _ => (q.demand.arguments[binder]?).map fun c => ⟨c.center,c.center,c.center⟩

/-- Existing ordinary body translation, or a derived typed native
source expression. This does not assert that every compound typed
expression has been lowered to the current C386 literal carrier. -/
inductive BodyWrite393 {s : State} {q : Request} (f : AuthoredBodyFrame393 s q)
    (body : Body) (target : Nat) : LiteralWriteSyntax → Prop where
  | ordinary {nf} :
      (∀ n ∈ (normalize (bodyPattern body)).variables, (f.slots body n).isSome = true) →
      translate (authoredRegistry s.current).constructors
        (interpretation s.current.environment.source.snapshot)
        (normalize (bodyPattern body)) = some nf →
      BodyWrite393 f body target
        (.ordinary ⟨target,logical (bodyCapture q.demand f.names.input body) .actual nf⟩)
  | native {ctor pats args} :
      normalize (bodyPattern body) = .app ctor pats →
      NativeBodyRhs392 s (f.slots body) false (.app ctor pats) (.nominal ctor args) →
      BodyWrite393 f body target (.declared target (.app ctor pats) args)
  | tagged {tag ctor pats args} :
      normalize (bodyPattern body) = .variant tag (.app ctor pats) →
      NativeBodyRhs392 s (f.slots body) false (.app ctor pats) (.nominal ctor args) →
      BodyWrite393 f body target (.declared target (.variant tag (.app ctor pats)) args)

/-- Original named requested output at a real ordinal: no input
receipt and no equation identifying that receipt's payload. -/
structure AuthoredOutput393 {s : State} {q : Request} (f : AuthoredBodyFrame393 s q)
    (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles f.decl (q.demand.outputs[i]).name body
  write : LiteralWriteSyntax
  builds : BodyWrite393 f body (q.demand.outputs[i]).target write

def AuthoredOutput393.receipt {s q f i} (o : AuthoredOutput393 (s := s) (q := q) f i) : OrderedReceipt :=
  ⟨q.occurrence,i.val,q.demand.outputs[i],o.body,o.write⟩

theorem AuthoredOutput393.fixed {s q f i} (o : AuthoredOutput393 (s := s) (q := q) f i) :
    o.receipt.writesTarget := by
  cases o with
  | mk body supplied write builds =>
    cases builds <;> rfl

def emittedReceipts393 {s q} (f : AuthoredBodyFrame393 s q)
    (each : ∀ i, AuthoredOutput393 f i) : List OrderedReceipt :=
  List.ofFn fun i => (each i).receipt

def emittedEvent393 {s q} (f : AuthoredBodyFrame393 s q)
    (each : ∀ i, AuthoredOutput393 f i) : LiteralLocalEvent s q where
  declarationOrdinal := f.ordinal
  declaration := f.decl
  declaredAt := f.authored
  inScope := f.inScope
  captures := f.captures
  whereEntries := f.clauses
  whereCount := by simp [AuthoredBodyFrame393.clauses]
  whereAt := by
    intro i entry located
    have inspected := located
    simp only [AuthoredBodyFrame393.clauses,List.getElem?_map] at inspected
    cases found : f.decl.requirements[i]? with
    | none => simp [found] at inspected
    | some clause =>
      have same : f.whereFor clause = entry := Option.some.inj (by simpa only [found,Option.map_some] using inspected)
      cases same
      exact ⟨rfl,rfl⟩
  receipts := emittedReceipts393 f each
  receiptCount := by simp [emittedReceipts393]
  receiptAt := by
    intro i receipt located
    have bounded : i < (emittedReceipts393 f each).length :=
      (List.getElem?_eq_some_iff.mp located).1
    have actual : i < q.demand.outputs.length := by simpa [emittedReceipts393] using bounded
    let ix : Fin q.demand.outputs.length := ⟨i,actual⟩
    have same : (each ix).receipt = receipt := by
      have found := Option.some.inj ((List.getElem?_eq_getElem bounded).symm.trans located)
      simpa [emittedReceipts393,ix] using found
    cases same
    exact ⟨rfl,rfl,List.getElem?_eq_getElem actual,(each ix).supplied,(each ix).fixed⟩

theorem emitted_original_sequence393 {s q} (f : AuthoredBodyFrame393 s q)
    (each : ∀ i, AuthoredOutput393 f i) (i : Fin q.demand.outputs.length) :
    (emittedEvent393 f each).receipts[i.val]? = some (each i).receipt := by
  simp [emittedEvent393,emittedReceipts393]

/-- The concrete local fact, rather than an equality with an already
provided receipt. A general LocalSource rule must establish actual
source emission for every represented source shape. -/
inductive SameEventRhs393 {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (capture : Nat → Capture) (receipt : OrderedReceipt) : Prop where
  | ordinary (row : GeneralDeclarativeHead320.Equation) :
      receipt.written = .ordinary row →
      SourceEquation (authoredRegistry s.current)
        (interpretation s.current.environment.source.snapshot) q.demand
        event.declaration capture row →
      SameEventRhs393 event capture receipt
  | native :
      NativeAssociatedRhs392 event receipt.source receipt.requested.target receipt.written →
      SameEventRhs393 event capture receipt

theorem generated_original_rhs393 {s q} (f : AuthoredBodyFrame393 s q)
    (each : ∀ i, AuthoredOutput393 f i) (i : Fin q.demand.outputs.length) :
    SameEventRhs393 (emittedEvent393 f each) f.names.input (each i).receipt := by
  have source := (each i).supplied
  unfold AuthoredOutput393.receipt
  cases chosen : each i with
  | mk body supplied write derives =>
    cases derives with
    | ordinary supported translated =>
      exact .ordinary _ rfl
        ⟨q.demand.outputs[i],List.getElem_mem _,body,supplied,_,translated,rfl⟩
    | native authored formula =>
      exact .native (.direct authored formula)
    | tagged authored formula =>
      exact .native (.tagged authored formula)

theorem actual_generated_where_and_captures393 {s q} (f : AuthoredBodyFrame393 s q)
    (each : ∀ i, AuthoredOutput393 f i) :
    (emittedEvent393 f each).whereEntries.map LiteralWhereEntry.demand =
      GeneralDeclarativeEmissionForest322.children f.decl f.names f.placement ∧
    (emittedEvent393 f each).captures =
      ((f.decl.inputNames ++ f.decl.outputNames).map fun n => (n,f.names.input n)) := by
  exact ⟨by simp [emittedEvent393,AuthoredBodyFrame393.clauses,
    AuthoredBodyFrame393.whereFor,GeneralDeclarativeEmissionForest322.children],rfl⟩

private theorem capture_lookup_from_source_table393
    (names : Nat → Capture) (selected : List Nat)
    {name : Nat} (member : name ∈ selected) :
    (selected.map fun n => (n,names n)).lookup name = some (names name) := by
  induction selected with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : name = head
    · subst head
      simp
    · have more : name ∈ rest := (List.mem_cons.mp member).resolve_left same
      simp [List.lookup_cons,beq_eq_false_iff_ne.mpr same,ih more]

/-- From the generated where child itself, not a later model or an
assumed equality with an existing capture list. -/
theorem generated_where_binder_at_original_output393
    {s q} (f : AuthoredBodyFrame393 s q) (each : ∀ i, AuthoredOutput393 f i)
    (produced : f.decl.Produced)
    {binder : GeneralDeclarations.OutputBinder} (member : binder ∈ f.decl.outputBinders)
    (body : GeneralDeclarations.Equation) :
    ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : GeneralDeclarations.Equation)
      (out : GeneralSourceState.Output),
      (emittedEvent393 f each).whereEntries[i]? = some entry ∧
      entry.clause.id = binder.clause ∧
      entry.clause.outputs[j]? = some eqn ∧ eqn.id = binder.equation ∧
      eqn.rhs = .var binder.name ∧ entry.demand.outputs[j]? = some out ∧
      out.name = eqn.name ∧
      writtenBodySlot392 (emittedEvent393 f each) (.explicit body) binder.name =
        some ⟨out.target,out.target,out.target⟩ := by
  obtain ⟨clause,inDecl,clauseId,eqn,inClause,eqnId,rhs⟩ := produced binder member
  obtain ⟨i,pos⟩ := List.getElem?_of_mem inDecl
  obtain ⟨j,eqPos⟩ := List.getElem?_of_mem inClause
  let entry := f.whereFor clause
  let out := GeneralDeclarativeSourceEmission322.useOutput f.decl f.names (f.placement.targets clause) eqn
  have named : binder.name ∈ f.decl.outputNames := List.mem_map.mpr ⟨binder,member,rfl⟩
  have atEntry : (emittedEvent393 f each).whereEntries[i]? = some entry := by
    simp [emittedEvent393,AuthoredBodyFrame393.clauses,pos,entry]
  have atOut : entry.demand.outputs[j]? = some out := by
    simp [entry,AuthoredBodyFrame393.whereFor,GeneralDeclarativeSourceEmission322.demand,eqPos,out]
  have target : out.target = f.names.output binder.name := by
    simp [out,GeneralDeclarativeSourceEmission322.useOutput,GeneralDeclarationDemands.outputTarget,
      GeneralDeclarativeSourceEmission322.Names.old,rhs,normalize,named]
  have point : f.names.input binder.name = ⟨out.target,out.target,out.target⟩ := by
    rw [target]
    simp [AuthoredBodyFrame393.names,GeneralDeclarativeFrameReadback325.sourceNames,
      GeneralDeclarativeProducedNames325.table,named]
  refine ⟨i,j,entry,eqn,out,atEntry,clauseId,eqPos,eqnId,rhs,atOut,rfl,?_⟩
  have read := capture_lookup_from_source_table393 f.names.input _ (List.mem_append_right f.decl.inputNames named)
  simpa only [writtenBodySlot392,emittedEvent393,AuthoredBodyFrame393.captures,point] using read

/-- Actual body proof, not equality of integer names, supplies the kind. -/
theorem kinded_slot_in_native_body393 {s : State} {slots : Nat → Option Capture}
    {context : Bool} {p : CommonDeclaredNominalInspection.Parameter} {binder : Nat}
    {capture : Capture} {argument : Argument Nat}
    (slot : slots binder = some capture)
    (used : NativeBodyArg392 s slots context p (.var binder) argument) :
    TypedBodyCapture392 s capture p.kind := by
  cases used with
  | pointValue mode _ found typed =>
    cases Option.some.inj (slot.symm.trans found)
    simpa only [mode] using typed
  | intervalValue mode _ found typed =>
    cases Option.some.inj (slot.symm.trans found)
    simpa only [mode] using typed
  | pointRow mode _ found typed =>
    cases Option.some.inj (slot.symm.trans found)
    simpa only [mode] using typed
  | intervalRow mode _ found typed =>
    cases Option.some.inj (slot.symm.trans found)
    simpa only [mode] using typed

theorem generated_where_binder_kinded_rhs393
    {s q} (f : AuthoredBodyFrame393 s q) (each : ∀ i, AuthoredOutput393 f i)
    (produced : f.decl.Produced)
    {binder : GeneralDeclarations.OutputBinder} (member : binder ∈ f.decl.outputBinders)
    (body : GeneralDeclarations.Equation)
    {context : Bool} {p : CommonDeclaredNominalInspection.Parameter} {argument : Argument Nat}
    (used : NativeBodyArg392 s (f.slots (.explicit body)) context p (.var binder.name) argument) :
    ∃ (i j : Nat) (entry : LiteralWhereEntry) (eqn : GeneralDeclarations.Equation)
      (out : GeneralSourceState.Output),
      (emittedEvent393 f each).whereEntries[i]? = some entry ∧
      entry.clause.id = binder.clause ∧
      entry.clause.outputs[j]? = some eqn ∧ eqn.id = binder.equation ∧
      eqn.rhs = .var binder.name ∧ entry.demand.outputs[j]? = some out ∧
      out.name = eqn.name ∧ TypedBodyCapture392 s ⟨out.target,out.target,out.target⟩ p.kind := by
  obtain ⟨i,j,entry,eqn,out,atEntry,clauseId,atEqn,eqnId,rhs,atOut,sameName,allocated⟩ :=
    generated_where_binder_at_original_output393 f each produced member body
  exact ⟨i,j,entry,eqn,out,atEntry,clauseId,atEqn,eqnId,rhs,atOut,sameName,kinded_slot_in_native_body393 allocated used⟩

end Yulang.GeneralDeclarativeI65
