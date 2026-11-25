import Yulang.GeneralDeclarativeI65I74RigidRivalRestriction418
import Yulang.GeneralDeclarativeI65I74ExplicitPickOutput419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration Equation Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeInspect321 (Visit PatternK2 fieldPatterns variable_has_no_visit)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open Checker408 (Problem)
open ClosedResidual415 (ClosedRows)

-- This projection only reuses an established literal input-row reader.
-- No election, associated body, B6 read, or receipt uses this view.
def inputView (p : Problem) : Problem :=
  {p with root := {p.root with demand := {p.root.demand with outputs := []}}}

abbrev Rows (p : Problem) := ClosedRows p.state (inputView p).root

def pickSyntax (label field tail : Nat) : Pattern := .record label (.var field) (.var tail)
def pickCode (label field tail : Nat) : Expr := .record label (.variable field) (.variable tail)

structure PickDeclaration (p : Problem) (r : Rows p) where
  decl : Declaration
  ordinal : Nat
  authored : (authoredRegistry p.state.core.current).declarations[ordinal]? = some decl
  theOnlyOne : visible p.state.core p.root = [decl]
  role : ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role
  checked : Checked (authoredRegistry p.state.core.current)
  covered : GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered p.state.core.current.environment decl
  fieldBinder : Nat
  tailBinder : Nat
  distinct : fieldBinder ≠ tailBinder
  literal : decl.head = [pickSyntax r.x fieldBinder tailBinder]
  clauseFree : decl.requirements = []
  noOutputBinders : decl.outputBinders = []
  explicit : Equation
  exactlyWritten : decl.associated = [explicit]
  explicitRhs : explicit.rhs = .var fieldBinder

def PickDeclaration.capture {p r} (d : PickDeclaration p r) : Nat → Capture :=
  fun name => if name = d.fieldBinder then point r.intSlot
    else if name = d.tailBinder then point r.residual else emptyCapture403

theorem PickDeclaration.field {p r} (d : PickDeclaration p r) :
    d.capture d.fieldBinder = point r.intSlot := by simp [PickDeclaration.capture]

theorem PickDeclaration.tail {p r} (d : PickDeclaration p r) :
    d.capture d.tailBinder = point r.residual := by simp [PickDeclaration.capture,Ne.symm d.distinct]

def PickDeclaration.frame {p r} (d : PickDeclaration p r) : AuthoredBodyFrame393 p.state.core p.root :=
  ⟨d.ordinal,d.decl,d.authored,by simp [d.theOnlyOne],unusedPlacement403,d.capture⟩

theorem frame_keeps_original_pick_capture419 {p r} (d : PickDeclaration p r) (binder : Nat) :
    d.frame.names.input binder = d.capture binder := by
  simp [AuthoredBodyFrame393.names,PickDeclaration.frame,GeneralDeclarativeFrameReadback325.sourceNames,
    GeneralDeclarativeProducedNames325.table,Declaration.outputNames,d.noOutputBinders]

def PickDeclaration.sourceHead {p r} (d : PickDeclaration p r) :
    SourceHead p.state.core p.root d.decl := by
  have source : p.root.demand.arguments = [point r.root] := r.requested
  have compiled : translate (authoredRegistry p.state.core.current).constructors
      (interpretation p.state.core.current.environment.source.snapshot)
      (pickSyntax r.x d.fieldBinder d.tailBinder) = some (pickCode r.x d.fieldBinder d.tailBinder) := rfl
  refine .ordered d.capture ?_
  rw [source,d.literal]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,_,compiled,.direct (.structural ?_)⟩) .nil
  refine .record r.retainedSplit (.capture ?_ ?_) (.capture ?_ ?_)
  · simpa [d.field,point,GeneralDeclarativeHead320.byMode] using GeneralDeclarativeBounds319.Bound.refl r.intSlot
  · simpa [d.field,point,GeneralDeclarativeHead320.byMode] using GeneralDeclarativeBounds319.Bound.refl r.intSlot
  · simpa [d.tail,point,GeneralDeclarativeHead320.byMode] using GeneralDeclarativeBounds319.Bound.refl r.residual
  · simpa [d.tail,point,GeneralDeclarativeHead320.byMode] using GeneralDeclarativeBounds319.Bound.refl r.residual

theorem raw_root_safety_on_original_demand419 {p : Problem} (r : Rows p)
    (safe : ¬ AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.root) :
    ¬ RootCycle p.state p.root := by
  have args : p.root.demand.arguments = [point r.root] := r.requested
  rintro ⟨argument,member,cyclic⟩
  rw [args] at member
  cases List.mem_singleton.mp member
  exact safe cyclic

theorem pick_binder_fields_do_not_look_inside_the_original_value419
    {view : GeneralDeclarativeK2Graph321.View} {root label field tail site : Nat}
    (path : Visit view root (pickCode label field tail) site) : site = root := by
  change Visit view root (.record label (.variable field) (.variable tail)) site at path
  cases path with
  | here => rfl
  | field _ _ pattern inner =>
    simp [fieldPatterns] at pattern
    rw [pattern.2] at inner
    exact False.elim (variable_has_no_visit inner)

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
