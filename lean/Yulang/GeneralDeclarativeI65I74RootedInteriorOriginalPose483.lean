import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483
import Yulang.GeneralDeclarativeI65I74ScopedRouteSound480

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (PriorPhase Site Trail readRoute)
open PreparedDeclarations463 (CheckedTable PrecheckedHead)
open LiteralVisits473 (StepWire written_pose_append_is_exact)
open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence)
open ObservationAlternatives473 (Positions oldPosition)
open InputCoordinates475 (registryAt oneCompiledStep477)

theorem original_ast_location_replays_the_exact_full_geom_trail
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel}
    {first last : Site s pos} {steps indices bit}
    (selected : Trail s pos rel first steps indices last bit) :
    atSource first.pattern (steps.flatMap StepWire.written) = some last.pattern := by
  induction selected with
  | stop => rfl
  | step hop _ _ _ tail =>
    rw [List.flatMap_cons,written_pose_append_is_exact,literal_occurrence hop.typed.writtenFrom,hop.written]
    exact tail

/-- Report identity is a fact about the unchanged problem and literal
original selectors. Its endpoints cannot be reconstructed merely from
the quotient classes of the paired presentations. -/
theorem rooted_report_fields_point_to_real_original_declaration_and_ast
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {wire : RootedInteriorWire n}
    (out : RootedInteriorReceipt p gd pos rel basis wire) :
    ∃ (head : PrecheckedHead (p := p.old) gd) (finish : Site p.old.state.core pos) (bit : Bool),
      visible p.old.state.core p.old.root = [head.orig.declaration] ∧
      (registryAt p)[wire.route.declarationOrdinal]? = some head.orig.declaration ∧
      head.orig.location.headArgument = wire.route.argument ∧
      atSource head.orig.original (wire.route.trail.tail.flatMap (fun entry => entry.1.written)) =
        some finish.pattern ∧
      out.report =
        ⟨⟨p.old.root.occurrence,head.orig.declaration.id,wire.route.declarationOrdinal⟩,
          wire.route.argument,wire.route.trail.tail.flatMap (fun entry => entry.1.written),
          wire.route.trail.tail.map (fun entry => oneCompiledStep477 entry.1.action),
          oldPosition pos finish.index,bit⟩ := by
  obtain ⟨head,first,finish,_,bit,visibleScope,registry,arg,headAt,_,_,_,_,_,_,_,_,trail,exact⟩ :=
    Producer479.a_checked_route_reflects_one_actual_safe_prefix_and_exact_terminal480 out.exactReport
  have literal := original_ast_location_replays_the_exact_full_geom_trail trail
  rw [headAt] at literal
  refine ⟨head,finish,bit,visibleScope,registry,arg,?_,exact⟩
  simpa only [List.flatMap_map,Function.comp_def] using literal

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
