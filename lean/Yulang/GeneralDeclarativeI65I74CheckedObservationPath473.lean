import Yulang.GeneralDeclarativeI65I74LiteralVisitCoordinates473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open ObservationAlternatives473 (Place Positions oldPosition graphOf readAlternatives observedInputPlace)
open ObservationSyntax471 (Slot FieldOrigin SourceTyping confirmedAddress)
open QuotientObservation471 (ConeWire Wire ReturnsUpToEquality)
open WrittenPattern460.PhysicalOrigin (Pose)

abbrev OwnState := GeneralDeclarativeI65.State

structure Checkpoint (n : Nat) where
  which : Fin n
  m : Nat
  k : Nat
  scope : ConeWire n m
  partition : Wire m k

structure PathWire (n : Nat) where
  here : Checkpoint n
  rest : List (StepWire × Checkpoint n)

def readCheck (s : OwnState) (pos : Positions n)
    (certs : List (Fin n × Fin n)) (whereAt : Place) (c : Checkpoint n) : Option Bool :=
  if oldPosition pos c.which = whereAt then
    readAlternatives s pos certs c.which c.scope c.partition
  else none

theorem checkpoint_does_not_substitute_a_place_or_change_its_bit
    {s : OwnState} {pos : Positions n} {certs : List (Fin n × Fin n)}
    {whereAt : Place} {checkpoint : Checkpoint n} {b : Bool}
    (ran : readCheck s pos certs whereAt checkpoint = some b) :
    oldPosition pos checkpoint.which = whereAt ∧ (b = true ↔ ReturnsUpToEquality (graphOf s pos) checkpoint.which) := by
  unfold readCheck at ran
  split at ran
  · rename_i anchored
    exact ⟨anchored,(ObservationAlternatives473.all_actual_alternatives_have_a_real_bisimilar_source_coordinate ran).1⟩
  · cases ran

def appendToInline (place : Place) (selection : Slot) (raw : Expr) : Option Place :=
  match place with
  | .logical _ => none
  | .rowPos atRow before =>
    match raw with
    | .variable _ => none
    | _ => some (.rowPos atRow (before ++ [selection]))

inductive ScopedPath (s : OwnState) (positions : Positions n) :
    Place → Pattern → Expr → Expr → PathWire n → List Pose → Fin n → Bool → Prop where
  | stop : oldPosition positions c.which = pos →
      (b = true ↔ ReturnsUpToEquality (graphOf s positions) c.which) →
      ScopedPath s positions pos p query raw ⟨c,[]⟩ [] c.which b
  | step {move : StepWire} (derived : ReadStep s move p query raw) :
      oldPosition positions c.which = pos →
      ¬ReturnsUpToEquality (graphOf s positions) c.which →
      appendToInline pos (childSlot move.action) derived.actualRawChild = some next →
      ScopedPath s positions next derived.writtenChild derived.childQuery derived.actualRawChild
        ⟨follow,tail⟩ written final b →
      ScopedPath s positions pos p query raw ⟨c,(move,follow)::tail⟩ (move.written ++ written) final b

structure TypedPathResult (s : OwnState) (positions : Positions n)
    (pos : Place) (p : Pattern) (query raw : Expr) (wire : PathWire n) where
  suffix : List Pose
  final : Fin n
  bit : Bool
  visits : ScopedPath s positions pos p query raw wire suffix final bit

def readLiteralPath (s : OwnState) (positions : Positions n) (relation : List (Fin n × Fin n))
    (pos : Place) (p : Pattern) (query raw : Expr) (wire : PathWire n) :
    Option (TypedPathResult s positions pos p query raw wire) :=
  match wire with
  | ⟨here,[]⟩ =>
    match checked : readCheck s positions relation pos here with
    | none => none
    | some b =>
      have sound := checkpoint_does_not_substitute_a_place_or_change_its_bit checked
      some ⟨[],here.which,b,.stop sound.1 sound.2⟩
  | ⟨here,(move,follow)::tail⟩ =>
    match checked : readCheck s positions relation pos here with
    | some false => do
      let step ← readLiteralVisitStep s p query raw move
      match next : appendToInline pos (childSlot move.action) step.actualRawChild with
      | none => none
      | some atNext =>
        let later ← readLiteralPath s positions relation atNext step.writtenChild step.childQuery step.actualRawChild
          ⟨follow,tail⟩
        have sound := checkpoint_does_not_substitute_a_place_or_change_its_bit checked
        pure ⟨move.written ++ later.suffix,later.final,later.bit,.step step sound.1
          (fun cp => Bool.false_ne_true (sound.2.mpr cp)) next later.visits⟩
    | _ => none
termination_by wire.rest

theorem scoped_path_reports_the_actual_terminal_not_reachability
    {s : OwnState} {positions : Positions n} {p query raw wire pos suffix final bit}
    (trace : ScopedPath s positions pos p query raw wire suffix final bit) :
    bit = true ↔ ReturnsUpToEquality (graphOf s positions) final := by
  induction trace with
  | stop _ correct => exact correct
  | step _ _ _ _ _ ih => exact ih

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open WrittenPattern460.PhysicalOrigin (atSource)
open ObservationSyntax471 (FieldOrigin SourceTyping confirmedAddress CheckedFieldBit AttachedFieldWire472 readFieldOrigin readTyping gateFromAttachedAuthor472)
open ObservationAlternatives473 (observedInputPlace Place Positions oldPosition)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open WrittenPattern460.PhysicalOrigin (Pose)
open GeneralDeclarationPatterns (Pattern)

theorem scoped_literal_correspondence_recovers_original_and_raw_finite_prefix
    {s : OwnState} {positions : Positions n} {p query raw wire pos suffix final bit}
    (trace : ScopedPath s positions pos p query raw wire suffix final bit) :
    ∃ pat code term,
      Visit s p query raw (wire.rest.map Prod.fst) pat code term ∧
      suffix = (wire.rest.map Prod.fst).flatMap StepWire.written := by
  induction trace with
  | stop =>
    exact ⟨_,_,_,.stop,rfl⟩
  | step current _ _ _ _ ih =>
    obtain ⟨pat,code,term,visit,path⟩ := ih
    exact ⟨pat,code,term,.walk current visit,by simp [path]⟩

structure NestedFieldReport (n : Nat) where
  occurrence : List Nat
  declarationId : Nat
  declarationOrdinal : Nat
  actualWritten : List Pose
  physicalSite : Place
  bit : Bool
  deriving DecidableEq

def terminalIsField (wire : PathWire n) : Bool :=
  match wire.rest.getLast? with
  | none => true
  | some (step,_) =>
    match step.action with
    | .field _ => true
    | _ => false

def readNestedAuthoredField {n : Nat} (p : FullProblem) (manifest : Table)
    (gd : CheckedTable p.old.state.core.current) (input : AttachedFieldWire472) (positions : Positions n)
    (relation : List (Fin n × Fin n)) (outer : Checkpoint n) (path : PathWire n) :
    Option (NestedFieldReport n) := do
  if !terminalIsField path then none else
    let a ← attach p.state.base.core.current.ordinary manifest
    let f ← readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a)
    let _ ← readTyping f
    match confirmedAddress f with
    | .named _ => none
    | .inline ordinal first =>
      match readCheck p.old.state.core positions relation (.logical f.head.orig.capture.lower) outer with
      | some false => do
        let v ← readLiteralPath p.old.state.core positions relation
          (.rowPos ordinal first) f.sourcePattern f.selectedQuery f.actualPayload path
        pure ⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,
          input.path ++ v.suffix,oldPosition positions v.final,v.bit⟩
      | _ => none

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
