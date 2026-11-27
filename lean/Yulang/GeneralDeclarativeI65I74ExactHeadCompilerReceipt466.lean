import Yulang.GeneralDeclarativeI65I74ReadOldCaptureReceipt466
import Yulang.GeneralDeclarativeI65I74ScopedHeadCompileAtPose466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466ExactOriginalHeadOldReceipt
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.Checker408 (Problem)
open Yulang.GeneralDeclarativeI65.I72.AuthoredInspectQuery456 (compileQuery compile_query_preserves_legacy)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose atSource)
open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeOrigins321 (Supported restriction)
open Yulang.GeneralDeclarativeNestedView332 (Sources)
open Yulang.GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Yulang.GeneralSourceMetadataRows291 (interpretation)
open Yulang.GeneralDeclarationPatterns (normalize)
open Yulang.C466WrittenBinderCoordinates
open Yulang.C466HeadCompileAtPose

/-- This only composes exact already-existing readers on the same actual
source capture and compiler frame. An emitted legacy ordinary row is still
not an I65 native Origin or an alteration of the compiler phase. -/
theorem one_actual_source_head_pins_legacy_assembly_and_modern_written_binder
    {p : Problem} (head : OriginalHead p) {complete : Nat → Prop}
    {legacy : Supported p.state.core.current.ordinary complete}
    (auth : Sources (restriction legacy)) (protect : List Nat) (job : Nat)
    (r : OldCaptureReceipt)
    (read : readOldCaptureReceipt p.state.core.current.ordinary auth
        (authoredRegistry p.state.core.current).constructors
        (interpretation p.state.core.current.environment.source.snapshot)
        head.capture protect head.original job = some r) :
    oldCompile p.state.core (normalize head.original) = some head.code ∧
    r.after.equations[r.rawOrdinal]? = some (⟨r.target,r.captured.term⟩ : Equation) ∧
    atSource (normalize head.original) r.written = some (.var r.captured.binder) ∧
    codeAt head.code r.written = some (.variable r.captured.binder) := by
  obtain ⟨code,uses,old,_,_,_,_,_⟩ := (exact_old_capture_execution_has_data_only_receipt ..).mp read
  have same := Option.some.inj ((compile_query_preserves_legacy p.state.core _ _ old).symm.trans
    ((Yulang.GeneralDeclarativeI65.I72.AuthoredInspectQuery456.compile_query_exact ..).mpr head.compiled))
  obtain ⟨atRaw,atPattern⟩ := a_receipt_really_names_the_original_capture_and_the_appended_ordinary_row read
  have shared := original_head_keeps_every_literal_query_address head r.written
  rw [atPattern] at shared
  refine ⟨same ▸ old,atRaw,atPattern,?_⟩
  exact shared.symm

theorem no_legacy_materializer_receipt_can_begin_at_a_modern_only_head_pose
    {p : Problem} (head : OriginalHead p) {legacySource : Yulang.GeneralDeclarativeHead320.State}
    (auth : Sources legacySource) (protect : List Nat) (job : Nat)
    {poses : List Pose} {inner : Yulang.GeneralDeclarationPatterns.Pattern}
    (arrived : atSource (normalize head.original) poses = some inner)
    (newOnly : oldCompile p.state.core inner = none) :
    readOldCaptureReceipt p.state.core.current.ordinary auth
      (authoredRegistry p.state.core.current).constructors
      (interpretation p.state.core.current.environment.source.snapshot)
      head.capture protect head.original job = none := by
  have missing : oldCompile p.state.core (normalize head.original) = none :=
    a_modern_only_pose_obstructs_any_old_compilation_of_the_whole_source arrived newOnly
  unfold oldCompile at missing
  simp [readOldCaptureReceipt,missing,Option.bind]

end Yulang.C466ExactOriginalHeadOldReceipt
