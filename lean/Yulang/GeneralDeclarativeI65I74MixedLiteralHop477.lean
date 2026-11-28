import Yulang.GeneralDeclarativeI65I74MixedGraphEdge477
import Yulang.GeneralDeclarativeI65I74LocatedUniqueOrdinal477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open LiteralVisits473 (StepWire ReadStep Checkpoint readCheck readLiteralVisitStep
  written_pose_append_is_exact childSlot independent_step_derivation_replays_its_original_addresses
  checkpoint_does_not_substitute_a_place_or_change_its_bit)
open ObservationAlternatives473
open ObservationSyntax471 (Slot descend)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

structure MixedPoint477 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (table : Positions n) (rel : List (Fin n × Fin n)) where
  source : Pattern
  code : Expr
  pose : List Pose
  written : atSource r.head.orig.original pose = some source
  compiled : List QueryStep476
  raw : Expr
  place : Place
  checkpoint : Checkpoint n
  stored : readTermAt p.old.state.core table checkpoint.which = some raw
  bit : Bool
  checked : readCheck p.old.state.core table rel place checkpoint = some bit

inductive MixedOrigin477 (trace : LocatedCapture476 rows) (path : List QueryStep476) (target : Position) :
    Expr → Place → Expr → Type where
  | named {n : Nat} (i : Nat) (stamp : LocatedMark476 rows)
      (found : trace.marks[i]? = some stamp) (address : stamp.path = path)
      (name : n = stamp.exposure.name)
      (ordinal : target.oldOrdinal = stamp.exposure.picked.raw) :
      MixedOrigin477 trace path target (.variable n) (.logical n) stamp.exposure.picked.row.right
  | inline {raw : Expr} {i : Nat} {before : List Slot}
      (literal : ∀ n, raw ≠ .variable n) :
      MixedOrigin477 trace path target raw (.rowPos i before) raw

structure MixedArrival477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    (trace : LocatedCapture476 w.offered) (point : MixedPoint477 r table rel)
    (step : StepWire) (next : Checkpoint n) where
  safe : point.bit = false
  accepted : ReadStep p.old.state.core step point.source point.code point.raw
  whereAt : Place
  raw : Expr
  origin : MixedOrigin477 trace (point.compiled ++ [oneCompiledStep477 step.action])
      (table.cells.get next.which) accepted.actualRawChild whereAt raw
  target : whereAt = anchorFor (table.cells.get point.checkpoint.which) (childSlot step.action)
      accepted.actualRawChild
  stored : readTermAt p.old.state.core table next.which = some raw
  bit : Bool
  checked : readCheck p.old.state.core table rel whereAt next = some bit

def MixedArrival477.finish {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {point : MixedPoint477 r table rel}
    {step : StepWire} {next : Checkpoint n}
    (hop : MixedArrival477 trace point step next) : MixedPoint477 r table rel :=
  ⟨hop.accepted.writtenChild,hop.accepted.childQuery,point.pose++step.written,
    by rw [written_pose_append_is_exact,point.written]; exact literal_occurrence hop.accepted.writtenFrom,
    point.compiled++[oneCompiledStep477 step.action],hop.raw,hop.whereAt,next,
    hop.stored,hop.bit,hop.checked⟩

theorem mixed_arrival_is_exact_edge_and_source_is_safe477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {point : MixedPoint477 r table rel}
    {step : StepWire} {next : Checkpoint n}
    (hop : MixedArrival477 trace point step next) :
    next.which ∈ successors (graphOf p.old.state.core table) point.checkpoint.which ∧
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) point.checkpoint.which := by
  have dest := (checkpoint_does_not_substitute_a_place_or_change_its_bit hop.checked).1
  refine ⟨positional_pin_forces_the_same_actual_edge477 point.checked point.stored hop.accepted
    (dest.trans hop.target),?_⟩
  intro cycle
  have b := (checkpoint_does_not_substitute_a_place_or_change_its_bit point.checked).2.mpr cycle
  rw [hop.safe] at b
  cases b


private theorem nonvariable_anchor_is_lexical477 (parent : Position) (slot : Slot)
    (raw : Expr) (lit : ∀ n, raw ≠ .variable n) :
    ∃ i path, anchorFor parent slot raw = .rowPos i path := by
  cases raw with
  | «variable» key => exact (lit key rfl).elim
  | primitive | nominal | record | variant | join =>
    cases z : parent.tag with
    | logical name => exact ⟨parent.oldOrdinal,[slot],by simp [anchorFor,z]⟩
    | rowPos i path => exact ⟨i,path++[slot],by simp [anchorFor,z]⟩

private def selectInline477 {rows} (trace : LocatedCapture476 rows) (path : List QueryStep476)
    (parent target : Position) (slot : Slot) (child : Expr) (lit : ∀ n, child ≠ .variable n) :
    Option ((raw : Expr) × MixedOrigin477 trace path target child (anchorFor parent slot child) raw) := by
  cases h : anchorFor parent slot child with
  | rowPos i before => exact some ⟨child,.inline lit⟩
  | logical n => exact none

def selectMixedOrigin477 {rows} (trace : LocatedCapture476 rows) (path : List QueryStep476)
    (parent target : Position) (slot : Slot) (child : Expr) :
    Option ((raw : Expr) × MixedOrigin477 trace path target child (anchorFor parent slot child) raw) :=
  match child with
  | .variable n => do
    let ordinal ← exactMarkOrdinal477 path trace
    match found : trace.marks[ordinal]? with
    | none => none
    | some stamp =>
      if address : stamp.path = path then
        if same : n = stamp.exposure.name then
          if old : target.oldOrdinal = stamp.exposure.picked.raw then
            some ⟨stamp.exposure.picked.row.right,.named ordinal stamp found address same old⟩
          else none
        else none
      else none
  | .primitive k args => selectInline477 trace path parent target slot (.primitive k args) (by intro n h; cases h)
  | .nominal k args => selectInline477 trace path parent target slot (.nominal k args) (by intro n h; cases h)
  | .record k x y => selectInline477 trace path parent target slot (.record k x y) (by intro n h; cases h)
  | .variant k x => selectInline477 trace path parent target slot (.variant k x) (by intro n h; cases h)
  | .join x y => selectInline477 trace path parent target slot (.join x y) (by intro n h; cases h)

def readMixedArrival477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    (trace : LocatedCapture476 w.offered) (point : MixedPoint477 r table rel)
    (wire : StepWire) (next : Checkpoint n) :
    Option (MixedArrival477 trace point wire next) :=
  if safe : point.bit = false then do
    let step ← readLiteralVisitStep p.old.state.core point.source point.code point.raw wire
    let k := childSlot wire.action
    let parent := table.cells.get point.checkpoint.which
    let destination ← selectMixedOrigin477 trace (point.compiled++[oneCompiledStep477 wire.action])
      parent (table.cells.get next.which) k step.actualRawChild
    let place := anchorFor parent k step.actualRawChild
    match stored : readTermAt p.old.state.core table next.which with
    | none => none
    | some actual =>
      if same : eqExpr actual destination.1 = true then
        match checked : readCheck p.old.state.core table rel place next with
        | none => none
        | some bit => some ⟨safe,step,place,destination.1,destination.2,rfl,
          by rw [(eq_expr ..).mp same] at stored; exact stored,bit,checked⟩
      else none
  else none

theorem checked_mixed_hop_keeps_compiled_and_original_paths477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {point : MixedPoint477 r table rel}
    {step : StepWire} {next : Checkpoint n}
    (ok : MixedArrival477 trace point step next) :
    (ok.finish).pose = point.pose ++ step.written ∧
    (ok.finish).compiled = point.compiled ++ [oneCompiledStep477 step.action] ∧
    ((ok.finish).bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) next.which) :=
  ⟨rfl,rfl,(checkpoint_does_not_substitute_a_place_or_change_its_bit ok.checked).2⟩



theorem checked_named_origin_selection_computes_existing_exact_stamp477
    {rows} (trace : LocatedCapture476 rows) (path : List QueryStep476)
    (parent target : Position) (s : Slot)
    {name i : Nat} {stamp : LocatedMark476 rows}
    (paths : (trace.marks.map LocatedMark476.path).Nodup)
    (found : trace.marks[i]? = some stamp) (address : stamp.path = path)
    (same : name = stamp.exposure.name) (ord : target.oldOrdinal = stamp.exposure.picked.raw) :
    selectMixedOrigin477 trace path parent target s (.variable name) =
      some ⟨stamp.exposure.picked.row.right,.named i stamp found address same ord⟩ := by
  have index := literal_ordinal_lookup_replays_every_existing_mark477 paths found address
  simp only [selectMixedOrigin477,index,bind,Option.bind]
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i other read
    have equal := Option.some.inj (read.symm.trans found)
    subst other
    simp [address,same,ord]

private theorem checked_inline_origin_selection_computes_existing_literal477
    {rows} (trace : LocatedCapture476 rows) (path : List QueryStep476)
    (parent target : Position) (s : Slot) (child : Expr)
    (lit : ∀ n, child ≠ .variable n) :
    ∃ (orig : MixedOrigin477 trace path target child (anchorFor parent s child) child),
      selectMixedOrigin477 trace path parent target s child = some ⟨child,orig⟩ := by
  obtain ⟨tag,old⟩ := parent
  cases child with
  | «variable» n => exact (lit n rfl).elim
  | primitive | nominal | record | variant | join =>
    cases tag <;> exact ⟨_,rfl⟩

theorem mixed_origin_selection_reflects_both_literal_cases477
    {rows} (trace : LocatedCapture476 rows) (path : List QueryStep476)
    (parent target : Position) (s : Slot) (child : Expr)
    {place raw} (origin : MixedOrigin477 trace path target child place raw)
    (paths : (trace.marks.map LocatedMark476.path).Nodup) :
    ∃ selected, selectMixedOrigin477 trace path parent target s child = some selected ∧ selected.1 = raw := by
  cases origin with
  | named i stamp found address same ord =>
    exact ⟨_,checked_named_origin_selection_computes_existing_exact_stamp477 trace path parent target s paths found address same ord,rfl⟩
  | inline lit =>
    obtain ⟨orig,read⟩ := checked_inline_origin_selection_computes_existing_literal477 trace path parent target s child lit
    exact ⟨_,read,rfl⟩



theorem mixed_arrival_replays_its_checked_bit477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {point : MixedPoint477 r table rel}
    {wire : StepWire} {next : Checkpoint n}
    (actualTrace : readLocatedAtHead476 r = some trace)
    (hop : MixedArrival477 trace point wire next) :
    ∃ replay, readMixedArrival477 trace point wire next = some replay ∧
      replay.bit = hop.bit ∧ replay.raw = hop.raw ∧ replay.whereAt = hop.whereAt ∧
      replay.finish = hop.finish := by
  have unique := actual_head_capture_has_unique_compiled_paths477 r actualTrace
  have literal := independent_step_derivation_replays_its_original_addresses hop.accepted
  obtain ⟨found,identified,source⟩ := mixed_origin_selection_reflects_both_literal_cases477 trace
    (point.compiled++[oneCompiledStep477 wire.action])
    (table.cells.get point.checkpoint.which) (table.cells.get next.which) (childSlot wire.action)
    hop.accepted.actualRawChild hop.origin unique
  have rawFit : readTermAt p.old.state.core table next.which = some found.1 := by
    rw [source]
    exact hop.stored
  have destFit : readCheck p.old.state.core table rel
      (anchorFor (table.cells.get point.checkpoint.which) (childSlot wire.action) hop.accepted.actualRawChild)
      next = some hop.bit := hop.target ▸ hop.checked
  unfold readMixedArrival477
  simp only [hop.safe,dite_true,literal,identified,bind,Option.bind]
  split
  · rename_i no
    rw [rawFit] at no
    contradiction
  · rename_i actual rawHas
    have same := Option.some.inj (rawHas.symm.trans rawFit)
    subst actual
    have ok : eqExpr found.1 found.1 = true := (eq_expr ..).mpr rfl
    simp only [ok,dite_true]
    split
    · rename_i no
      rw [destFit] at no
      contradiction
    · rename_i bit eq
      have exactBit := Option.some.inj (eq.symm.trans destFit)
      subst bit
      refine ⟨_,rfl,rfl,source,hop.target.symm,?_⟩
      simp only [MixedArrival477.finish,MixedPoint477.mk.injEq]
      simp [source,hop.target]

def mixedPointFromChosenNamed477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) : MixedPoint477 r table rel := by
  have replay : readAlternatives p.old.state.core table rel c.checkpoint.which c.checkpoint.scope
      c.checkpoint.partition = some c.bit := by simpa [readCheck,c.actual.1] using c.returned
  obtain ⟨_,known⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  have stored : readTermAt p.old.state.core table c.checkpoint.which =
      some c.mark.exposure.picked.row.right := by
    -- Reading the indicated old ordinal recovers the same literal body.
    -- The cone guarantees a successful observation, while the capture
    -- independently fixes both the original raw and authored occurrences.
    obtain ⟨raw,_,_,_,read,_,_,_⟩ :=
      a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
    obtain ⟨row,atRow,_,spelling⟩ :=
      a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row c.actual.1 read
    have same := (named_checkpoint_carries_exact_written_raw_and_author_occurrences477 c).2.1
    rw [c.actual.2] at atRow
    have e := Option.some.inj (atRow.symm.trans same)
    rw [←e,spelling]
    exact read
  exact ⟨c.source,c.code,c.pose,c.written,c.mark.path,c.mark.exposure.picked.row.right,
    .logical c.mark.exposure.name,c.checkpoint,stored,c.bit,c.returned⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

