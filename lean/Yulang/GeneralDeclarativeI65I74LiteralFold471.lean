import Yulang.GeneralDeclarativeI65I74PreparedHeadStart463
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.CommonRoleGraphBisimulation

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open RecordTraversal455 (termInspects term_inspects_exact455)
open GeneralDeclarativeInspect321 (Inspects)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)

private abbrev Raw := GeneralDeclarativeHead320.State

structure FoldWire where
  ownerOrdinal : Nat
  pointOrdinal : Nat
  cycle : FieldCycleWire

/-- A first closed-record field on both sides. This audits a literal
one-unfold correspondence only, not general bisimulation or a new raw edge. -/
def readFirstClosedField : Expr → Option (Nat × Expr)
  | .record label payload (.primitive .emptyRecord []) => some (label,payload)
  | _ => none

structure LiteralFold (s : Raw) (root : Nat) (query : Expr) (w : FoldWire) where
  owner : Equation
  point : Equation
  field : Nat
  inline : Expr
  requested : Expr
  selectedOwner : s.equations[w.ownerOrdinal]? = some owner
  selectedPoint : s.equations[w.pointOrdinal]? = some point
  ownerIsRoot : owner.left = root
  fieldAtSource : readFirstClosedField owner.right = some (field,inline)
  fieldAtQuery : readFirstClosedField query = some (field,requested)
  actualNonvariable : Inspects requested
  unfolded : inline = point.right
  rawCycle : AliasCycle s (observed s) point.left

/-- Use the real raw owner and point equations unchanged, and the field
actually selected by the compiled constructor. No whole-model test. -/
def readLiteralFold (s : Raw) (root : Nat) (query : Expr) (w : FoldWire) :
    Option (LiteralFold s root query w) :=
  match hs : s.equations[w.ownerOrdinal]?, hp : s.equations[w.pointOrdinal]? with
  | some a, some b =>
    match left : readFirstClosedField a.right, right : readFirstClosedField query with
    | some (x,payload),some (y,pat) =>
      if ok : a.left = root ∧ x = y ∧ termInspects pat = true ∧
          eqExpr payload b.right = true ∧ checkCycleAt412 s b.left w.cycle = true then
        some ⟨a,b,x,payload,pat,hs,hp,ok.1,left,ok.2.1.symm ▸ right,
          (term_inspects_exact455 _).mp ok.2.2.1,(eq_expr ..).mp ok.2.2.2.1,
          cycle_at_sound412 ok.2.2.2.2⟩
      else none
    | _,_ => none
  | _,_ => none

open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models environment)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)

theorem literal_fold_identifies_the_same_regular_value_in_each_ordinary_fit
    {s root query w} (a : LiteralFold s root query w)
    (m : Assignment) (fitted : Models s m) :
    Equivalent (m a.point.left).1 (value (environment m) .actual a.inline) := by
  rw [a.unfolded]
  exact fitted.2 a.point (List.mem_of_getElem? a.selectedPoint)

theorem positive_fold_keeps_original_raw_cycle_at_the_corresponding_point
    {s root query w} (a : LiteralFold s root query w) :
    AliasCycle s (observed s) a.point.left := a.rawCycle

theorem literal_fold_agrees_in_every_same_full_fit
    {s : FullState} {root query w}
    (a : LiteralFold s.base.core.current.ordinary root query w) (m : Model)
    (fit : FitsFull s m) :
    Equivalent (m.assignment a.point.left).1
      (value (environment m.assignment) .actual a.inline) ∧
    AliasCycle s.base.core.current.ordinary (observed s.base.core.current.ordinary) a.point.left :=
  ⟨literal_fold_identifies_the_same_regular_value_in_each_ordinary_fit a _ fit.1.1.1,a.rawCycle⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471


namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open PreparedDeclarations463
open WrittenPattern460.PhysicalOrigin (Pose atSource)
open Yulang.GeneralDeclarativeI65 (visible)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open RetainedFull445
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment)
open CommonNominalFullCarrier (Equivalent)

structure HeadWire where
  source : HeadAddress
  path : List Pose
  physical : FoldWire
  label : Nat
  binder : Nat

def occurrenceComparison (label : Nat) : Graph 2 :=
  fun _ => .structural label [1]

def occurrencePairs : List (Fin 2 × Fin 2) := [(0,1),(1,1)]

theorem comparison_is_closed_and_named_point_cyclic (label : Nat) :
    checkBisimulation (occurrenceComparison label) occurrencePairs = true ∧
    recursiveAt (occurrenceComparison label) 1 = true := by
  constructor
  · simp [checkBisimulation,occurrenceComparison,occurrencePairs,nodeCheck,childrenCheck]
  · apply (recursive_at_exact ..).mpr
    exact ⟨label,[1],rfl,1,List.mem_cons_self,.nil _⟩

structure HeadReceipt (p : FullProblem) (tab : CheckedTable p.old.state.core.current)
    (w : HeadWire) where
  head : PrecheckedHead tab
  headAddress : head.orig.location = w.source
  singleton : visible p.old.state.core p.old.root = [head.orig.declaration]
  folded : LiteralFold p.state.base.core.current.ordinary head.orig.capture.lower
    head.orig.code w.physical
  written : Pattern
  pathExact : w.path = [.payload]
  originalRecord : ∃ tail, head.orig.original = .record folded.field written tail
  writtenAt : atSource head.orig.original w.path = some written
  writtenCompile : AuthoredQuery p.old.state.core (normalize written) folded.requested
  selectedConstructor : readFirstClosedField folded.requested = some (w.label,.variable w.binder)
  namedConstructor : readFirstClosedField folded.point.right = some (w.label,.variable folded.point.left)

/-- The report is for the given authored first payload, not an old named hop
through the outer row. The observation relation uses no stored graph point
for the inline occurrence. This is a positive self-record fragment only. -/
def readHeadFold (p : FullProblem) (tab : CheckedTable p.old.state.core.current)
    (w : HeadWire) : Option (HeadReceipt p tab w) := do
  let a ← readPrecheckedHead tab w.source
  let f ← readLiteralFold p.state.base.core.current.ordinary a.orig.capture.lower a.orig.code w.physical
  match hs : a.orig.original with
  | .record l selected tail =>
    if ok : a.orig.location = w.source ∧
        visible p.old.state.core p.old.root = [a.orig.declaration] ∧ l = f.field ∧
        w.path = [.payload] then
      match cc : compileQuery p.old.state.core (normalize selected) with
      | none => none
      | some compiled =>
        if cert : eqExpr compiled f.requested = true ∧
            eqExpr f.requested (.record w.label (.variable w.binder) (.primitive .emptyRecord [])) = true ∧
            eqExpr f.point.right (.record w.label (.variable f.point.left) (.primitive .emptyRecord [])) = true then
          some ⟨a,ok.1,ok.2.1,f,selected,ok.2.2.2,⟨tail,ok.2.2.1 ▸ hs⟩,by
            rw [ok.2.2.2,hs]; rfl,
            (eq_expr ..).mp cert.1 ▸ (compile_query_exact ..).mp cc,by rw [(eq_expr ..).mp cert.2.1]; rfl, by rw [(eq_expr ..).mp cert.2.2]; rfl⟩
        else none
    else none
  | _ => none

theorem receipt_exact_selected_observations {p tab w} (r : HeadReceipt p tab w) :
    readFirstClosedField r.folded.inline = some (w.label,.variable r.folded.point.left) ∧
    readFirstClosedField r.folded.point.right = some (w.label,.variable r.folded.point.left) ∧
    checkBisimulation (occurrenceComparison w.label) occurrencePairs = true ∧
    recursiveAt (occurrenceComparison w.label) 1 = true :=
  ⟨r.folded.unfolded ▸ r.namedConstructor,r.namedConstructor,
    comparison_is_closed_and_named_point_cyclic w.label⟩

theorem head_receipt_same_original_fit {p tab w} (r : HeadReceipt p tab w)
    (m : Model) (fit : FitsFull p.state m) :
    Equivalent (m.assignment r.folded.point.left).1
      (value (environment m.assignment) .actual r.folded.inline) ∧
    AliasCycle p.state.base.core.current.ordinary
      (observed p.state.base.core.current.ordinary) r.folded.point.left :=
  literal_fold_agrees_in_every_same_full_fit r.folded m fit

structure Report where
  occurrence : List Nat
  declarationId : Nat
  role : Nat
  source : HeadAddress
  path : List Pose
  root : Nat
  selectedField : Nat
  representative : Nat
  deriving DecidableEq

def reportOf {p tab w} (r : HeadReceipt p tab w) : Report :=
  ⟨p.root.occurrence,r.head.orig.declaration.id,r.head.orig.declaration.role,
    r.head.orig.location,w.path,r.folded.owner.left,r.folded.field,r.folded.point.left⟩

def checkHeadReport (p : FullProblem) (tab : CheckedTable p.old.state.core.current)
    (w : HeadWire) (wanted : Report) : Bool :=
  (readHeadFold p tab w).any fun r => decide (reportOf r = wanted)

theorem checked_report_pinpoints_receipt {p tab w wanted}
    (accepted : checkHeadReport p tab w wanted = true) :
    ∃ r, readHeadFold p tab w = some r ∧ reportOf r = wanted := by
  unfold checkHeadReport at accepted
  cases seen : readHeadFold p tab w with
  | none => simp [seen] at accepted
  | some r => exact ⟨r,rfl,of_decide_eq_true (by simpa [seen] using accepted)⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RecordTraversal455 (termInspects term_inspects_exact455)
open RecordK2412 (checkCycleAt412)

theorem readFirstClosedField_shape {e label payload} :
    readFirstClosedField e = some (label,payload) →
    e = .record label payload (.primitive .emptyRecord []) := by
  intro ok
  unfold readFirstClosedField at ok
  split at ok
  · rename_i l p
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ok)
    rfl
  · cases ok

theorem literal_fold_replays {s root query w} (r : LiteralFold s root query w)
    (givenCycle : checkCycleAt412 s r.point.left w.cycle = true) :
    readLiteralFold s root query w = some r := by
  have inspect := (term_inspects_exact455 _).mpr r.actualNonvariable
  have same := (eq_expr ..).mpr r.unfolded
  unfold readLiteralFold
  split
  · rename_i a b ha hb
    have va := Option.some.inj (ha.symm.trans r.selectedOwner)
    have vb := Option.some.inj (hb.symm.trans r.selectedPoint)
    subst a b
    split
    · rename_i la src lb req hat hquery
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hat.symm.trans r.fieldAtSource))
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hquery.symm.trans r.fieldAtQuery))
      rw [dite_eq_left ⟨r.ownerIsRoot,rfl,inspect,same,givenCycle⟩]
    · rename_i fail
      exfalso
      exact fail _ _ _ _ r.fieldAtSource r.fieldAtQuery
  · rename_i fail
    exfalso
    exact fail _ _ r.selectedOwner r.selectedPoint

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open RetainedFull445
open PreparedDeclarations463
open GeneralDeclarativeI65 (Request)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeOrigins321 (Supported Backed Available)
open GeneralDeclarativeHead320 (Equation)
open WrittenPattern460.PhysicalOrigin (Pose)

/-- A separately supplied protocol for ordinary source evidence. Raw rows
still include pending equations; this gate must not accept them as a source.
The protocol is an external input, not a compiler-event producer. -/
structure SourceGate (p : FullProblem) where
  completed : Nat → Prop
  ledger : Supported p.state.base.core.current.ordinary completed
  Authenticates : List Nat → Nat → Equation → Prop
  Data : Type
  verify : List Nat → Nat → Equation → Data → Bool
  exact : ∀ q i row, (∃ w, verify q i row w = true) ↔ Authenticates q i row
  source : ∀ q i row, Authenticates q i row → ledger.derivesFrom row .source

structure SourceWire (g : SourceGate p) where
  field : HeadWire
  declarationOrdinal : Nat
  sourceToken : g.Data

structure SourceReceipt (g : SourceGate p) (tab : CheckedTable p.old.state.core.current)
    (w : SourceWire g) where
  field : HeadReceipt p tab w.field
  originalDecl : p.old.state.core.current.environment.source.declarations[w.declarationOrdinal]? =
    some field.head.orig.declaration
  authenticated : g.Authenticates p.root.occurrence w.field.physical.ownerOrdinal field.folded.owner

def readSourceFold {p : FullProblem} (g : SourceGate p) (tab : CheckedTable p.old.state.core.current)
    (w : SourceWire g) : Option (SourceReceipt g tab w) := do
  let r ← readHeadFold p tab w.field
  if original : p.old.state.core.current.environment.source.declarations[w.declarationOrdinal]? =
       some r.head.orig.declaration then
    if yes : g.verify p.root.occurrence w.field.physical.ownerOrdinal r.folded.owner w.sourceToken = true then
      some ⟨r,original,(g.exact ..).mp ⟨_,yes⟩⟩
    else none
  else none

structure SourceReport where
  head : Report
  declarationOrdinal : Nat
  deriving DecidableEq

def reportOfSource {p g tab w} (r : @SourceReceipt p g tab w) : SourceReport :=
  ⟨reportOf r.field,w.declarationOrdinal⟩

def checkSourceReport {p : FullProblem} (g : SourceGate p) (tab : CheckedTable p.old.state.core.current)
    (w : SourceWire g) (wanted : SourceReport) : Bool :=
  (readSourceFold g tab w).any fun r => decide (reportOfSource r = wanted)

theorem source_receipt_is_available_from_source {p g tab w} (r : @SourceReceipt p g tab w) :
    Backed g.ledger r.field.folded.owner :=
  ⟨.source,g.source _ _ _ r.authenticated,.source⟩

theorem unchecked_pending_row_cannot_be_a_source_receipt {p g tab w}
    (r : @SourceReceipt p g tab w)
    (pending : ∀ o, g.ledger.derivesFrom r.field.folded.owner o →
      ∃ d, o = .output d ∧ ¬g.completed d) : False := by
  obtain ⟨_,contra,_⟩ := pending .source (g.source _ _ _ r.authenticated)
  cases contra

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open PreparedDeclarations463
open RetainedFull445
open AuthoredInspectQuery456 (compile_query_exact)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open RecordK2412 (checkCycleAt412)

theorem head_fold_replays {p tab w} (r : HeadReceipt p tab w)
    (givenCycle : checkCycleAt412 p.state.base.core.current.ordinary
      r.folded.point.left w.physical.cycle = true) :
    readHeadFold p tab w = some r := by
  have head := each_prechecked_head_position_replays tab r.head
  rw [r.headAddress] at head
  have fold := literal_fold_replays r.folded givenCycle
  unfold readHeadFold
  simp only [head,bind,Option.bind,fold]
  obtain ⟨tail, original⟩ := r.originalRecord
  split
  · rename_i l selected other found
    have here := GeneralDeclarationPatterns.Pattern.record.inj (found.symm.trans original)
    rcases here with ⟨rfl,rfl,rfl⟩
    rw [dite_eq_left ⟨r.headAddress,r.singleton,rfl,r.pathExact⟩]
    split
    · rename_i missing
      rw [(compile_query_exact ..).mpr r.writtenCompile] at missing
      cases missing
    · rename_i compiled run
      have same := Option.some.inj (run.symm.trans ((compile_query_exact ..).mpr r.writtenCompile))
      subst compiled
      have source := readFirstClosedField_shape r.selectedConstructor
      have point := readFirstClosedField_shape r.namedConstructor
      rw [dite_eq_left ⟨(eq_expr ..).mpr rfl,(eq_expr ..).mpr source,(eq_expr ..).mpr point⟩]
  · rename_i miss
    exact (miss _ _ _ original).elim

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open PreparedDeclarations463
open RetainedFull445
open RecordK2412 (FieldCycleWire checkCycleAt412)
open RecordTraversal455 (naked_raw_cycle_has_finite_wire455)

def replaceCycle (w : HeadWire) (cycle : FieldCycleWire) : HeadWire :=
  { w with physical := {w.physical with cycle} }

def receiptWithCycle {p tab w} (r : HeadReceipt p tab w) (cycle : FieldCycleWire) :
    HeadReceipt p tab (replaceCycle w cycle) where
  head := r.head
  headAddress := r.headAddress
  singleton := r.singleton
  folded :=
    ⟨r.folded.owner,r.folded.point,r.folded.field,r.folded.inline,r.folded.requested,
      r.folded.selectedOwner,r.folded.selectedPoint,r.folded.ownerIsRoot,r.folded.fieldAtSource,
      r.folded.fieldAtQuery,r.folded.actualNonvariable,r.folded.unfolded,r.folded.rawCycle⟩
  written := r.written
  pathExact := r.pathExact
  originalRecord := r.originalRecord
  writtenAt := r.writtenAt
  writtenCompile := r.writtenCompile
  selectedConstructor := r.selectedConstructor
  namedConstructor := r.namedConstructor

theorem source_fold_replays {p g tab w} (r : @SourceReceipt p g tab w)
    (cycle : checkCycleAt412 p.state.base.core.current.ordinary
      r.field.folded.point.left w.field.physical.cycle = true)
    (gate : g.verify p.root.occurrence w.field.physical.ownerOrdinal r.field.folded.owner w.sourceToken = true) :
    readSourceFold g tab w = some r := by
  unfold readSourceFold
  simp only [head_fold_replays r.field cycle,bind,Option.bind,
    r.originalDecl,gate,dite_eq_left]

/-- The independent rule consists of the fields of the receipt, with raw K2
as an inductive fact and source authentication as a proposition. The older
cycle data and source token at the indices need not be valid. -/
def ScopedPositive {p : FullProblem} (g : SourceGate p)
    (tab : CheckedTable p.old.state.core.current) (wanted : SourceReport) : Prop :=
  ∃ (w : SourceWire g) (r : SourceReceipt g tab w), reportOfSource r = wanted

theorem scoped_positive_exact_finite_source_report {p : FullProblem} (g : SourceGate p)
    (tab : CheckedTable p.old.state.core.current) (wanted : SourceReport) :
    (∃ w, checkSourceReport g tab w wanted = true) ↔ ScopedPositive g tab wanted := by
  constructor
  · rintro ⟨w,yes⟩
    unfold checkSourceReport at yes
    cases rr : readSourceFold g tab w with
    | none => simp [rr] at yes
    | some r => exact ⟨w,r,of_decide_eq_true (by simpa [rr] using yes)⟩
  · rintro ⟨w,r,report⟩
    obtain ⟨cycle,closed⟩ := (naked_raw_cycle_has_finite_wire455 _ _).mp r.field.folded.rawCycle
    obtain ⟨token,backed⟩ := (g.exact ..).mpr r.authenticated
    let fresh : SourceWire g := ⟨replaceCycle w.field cycle,w.declarationOrdinal,token⟩
    let rf : SourceReceipt g tab fresh :=
      ⟨receiptWithCycle r.field cycle,r.originalDecl,r.authenticated⟩
    have yes := source_fold_replays rf closed backed
    have unchanged : reportOfSource rf = wanted := report
    exact ⟨fresh,by simp [checkSourceReport,yes,unchanged]⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471

namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open RetainedFull445
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeOrigins321 (Backed)

theorem scope_exact_regular_observation {p g tab w} (r : @SourceReceipt p g tab w) :
    ObservationallyEqual (occurrenceComparison w.field.label) 0 1 := by
  intro depth
  apply bisimulation_observations (occurrenceComparison w.field.label) occurrencePairs
      ((check_bisimulation_exact ..).mp (receipt_exact_selected_observations r.field).2.2.1)
  simp [occurrencePairs]

theorem source_report_has_actual_literal_position_and_same_fit {p g tab w wanted}
    (accepted : checkSourceReport g tab w wanted = true) :
    ∃ r : @SourceReceipt p g tab w,
      reportOfSource r = wanted ∧
      Backed g.ledger r.field.folded.owner ∧
      ObservationallyEqual (occurrenceComparison w.field.label) 0 1 ∧
      (∀ m : Model, FitsFull p.state m →
        Equivalent (m.assignment r.field.folded.point.left).1
          (value (environment m.assignment) .actual r.field.folded.inline)) := by
  unfold checkSourceReport at accepted
  cases rr : readSourceFold g tab w with
  | none => simp [rr] at accepted
  | some r =>
    exact ⟨r,of_decide_eq_true (by simpa [rr] using accepted),
      source_receipt_is_available_from_source r,scope_exact_regular_observation r,
      fun m fit => (head_receipt_same_original_fit r.field m fit).1⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
