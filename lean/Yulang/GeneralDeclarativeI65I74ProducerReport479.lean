import Yulang.GeneralDeclarativeI65I74ProducerTrail479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable readPrecheckedHead)
open InputCoordinates475 (rawAt registryAt oneCompiledStep477 SamePhaseInputObservation478)
open ObservationAlternatives473 (Positions oldPosition)
open LiteralVisits473 (StepWire terminalIsField pathEndsWithField)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeHead320 (Equation)

structure RouteWire (n : Nat) where
  argument : Nat
  declarationOrdinal : Nat
  trail : TrailWire n

def rootedInField {n : Nat} : List (StepWire × LiteralVisits473.Checkpoint n) → Bool
  | (⟨.field _,_⟩,_)::_ => true
  | _ => false

def readRoute {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (rel : List (Fin n × Fin n)) (w : RouteWire n) :
    Option SamePhaseInputObservation478 := do
  let chosen ← readPrecheckedHead (p := p.old) gd ⟨0,w.argument⟩
  if chosen.orig.location.headArgument = w.argument ∧
      visible p.old.state.core p.old.root = [chosen.orig.declaration] ∧
      (registryAt p)[w.declarationOrdinal]? = some chosen.orig.declaration then
    let selected := w.trail.cursor.which
    let start ← siteAt (s := p.old.state.core) (pos := positions) selected chosen.orig.original chosen.orig.code
    let row ← (rawAt p).equations[(positions.cells.get selected).oldOrdinal]?
    if oldPosition positions selected = .logical chosen.orig.capture.lower ∧
        row.left = chosen.orig.capture.lower ∧ eqExpr row.right start.term = true ∧
        rootedInField w.trail.tail = true ∧ terminalIsField ⟨w.trail.cursor,w.trail.tail⟩ = true then
      let (finish,sign) ← readTrail rel start w.trail
      pure ⟨⟨p.old.root.occurrence,chosen.orig.declaration.id,w.declarationOrdinal⟩,
        w.argument,w.trail.tail.flatMap (fun x => x.1.written),
        w.trail.tail.map (fun x => oneCompiledStep477 x.1.action),oldPosition positions finish.index,sign⟩
    else none
  else none

theorem materialize_independent_geometry_without_issuing_a_source479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (event : TypedInput p gd pos rel)
    (zero : event.head.orig.location.visibleOrdinal = 0) :
    ∃ w : RouteWire n, w.argument = event.head.orig.location.headArgument ∧
      w.declarationOrdinal = event.declarationOrdinal ∧ w.trail.cursor.which = event.root.index ∧
      w.trail.tail.map Prod.fst = ⟨.field event.firstLabel,event.firstPose⟩ :: event.tail ∧
      w.trail.tail.map (fun x => x.2.which) = event.first.index :: event.tailPoints ∧
      readRoute p gd pos rel w = some event.report := by
  have trail : Trail p.old.state.core pos rel event.root
      (⟨.field event.firstLabel,event.firstPose⟩ :: event.tail)
      (event.first.index :: event.tailPoints) event.final event.bit :=
    .step event.enters event.rootGuard event.rootSafe event.visits
  obtain ⟨w,loc,moves,places,replay⟩ := finite_trail_wire_replays_exact_selected_path479 trail
  let r : RouteWire n := ⟨event.head.orig.location.headArgument,event.declarationOrdinal,w⟩
  refine ⟨r,rfl,rfl,loc,moves,places,?_⟩
  have address : (⟨0,event.head.orig.location.headArgument⟩ : PreparedDeclarations463.HeadAddress) =
      event.head.orig.location := by
    cases seen : event.head.orig.location with
    | mk idx arg =>
      simpa [seen] using zero.symm
  have exactHead := PreparedDeclarations463.each_prechecked_head_position_replays gd event.head
  have start : siteAt (s := p.old.state.core) (pos := pos) w.cursor.which
      event.head.orig.original event.head.orig.code = some event.root := by
    rw [loc,←event.atHead.1,←event.atHead.2]
    exact siteAt_replays479 event.root
  have begins : rootedInField w.tail = true := by
    cases e : w.tail with
    | nil => simp [e] at moves
    | cons h t =>
      obtain ⟨same,_⟩ := List.cons.inj (by simpa only [e,List.map_cons] using moves)
      rcases h with ⟨hd,cp⟩
      change hd = _ at same
      rw [same]
      rfl
  have ends : terminalIsField ⟨w.cursor,w.tail⟩ = true := by
    apply LiteralVisits473.terminal_selector_is_exact.mpr
    change pathEndsWithField (w.tail.map Prod.fst)
    rw [moves]
    cases e : event.tail with
    | nil => simp [pathEndsWithField]
    | cons h t =>
      simpa [pathEndsWithField,e] using event.endsInField
  have sourcePath := congrArg (List.flatMap StepWire.written) moves
  have compiledPath := congrArg (List.map (oneCompiledStep477 ∘ StepWire.action)) moves
  simp only [readRoute,r,address,exactHead,bind,Option.bind]
  rw [ite_eq_left ⟨True.intro,event.single,event.registered⟩,start]
  simp only [loc,event.physicalRow,event.existingRoot]
  rw [ite_eq_left ⟨event.atPoint,event.rootOwns.1,(eq_expr ..).mpr event.rootOwns.2,begins,ends⟩,replay]
  have pose : w.tail.flatMap (fun x => x.1.written) =
      event.firstPose ++ event.tail.flatMap StepWire.written := by
    simpa only [List.flatMap_map,Function.comp_def,List.flatMap_cons] using sourcePath
  have code : w.tail.map (fun x => oneCompiledStep477 x.1.action) =
      .field event.firstLabel :: event.tail.map (oneCompiledStep477 ∘ StepWire.action) := by
    simpa only [List.map_map,Function.comp_def,List.map_cons,oneCompiledStep477] using compiledPath
  simp only [pure,TypedInput.report,pose,code]

end Yulang.GeneralDeclarativeI65.I72.Producer479
