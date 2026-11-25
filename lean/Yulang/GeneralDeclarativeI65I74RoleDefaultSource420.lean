import Yulang.GeneralDeclarativeI65I74RigidRivalRestriction418
import Yulang.GeneralDeclarativeI65I74ExplicitPickLocator419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open ExplicitPick419 (Rows pickSyntax pickCode)
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

structure DefaultDeclaration (p : Problem) (r : Rows p) where
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

def DefaultDeclaration.capture {p r} (d : DefaultDeclaration p r) : Nat → Capture :=
  fun name => if name = d.fieldBinder then point r.intSlot
    else if name = d.tailBinder then point r.residual else emptyCapture403

theorem DefaultDeclaration.field {p r} (d : DefaultDeclaration p r) :
    d.capture d.fieldBinder = point r.intSlot := by simp [DefaultDeclaration.capture]

theorem DefaultDeclaration.tail {p r} (d : DefaultDeclaration p r) :
    d.capture d.tailBinder = point r.residual := by simp [DefaultDeclaration.capture,Ne.symm d.distinct]

def DefaultDeclaration.frame {p r} (d : DefaultDeclaration p r) : AuthoredBodyFrame393 p.state.core p.root :=
  ⟨d.ordinal,d.decl,d.authored,by simp [d.theOnlyOne],unusedPlacement403,d.capture⟩

theorem frame_keeps_original_default_capture420 {p r} (d : DefaultDeclaration p r) (binder : Nat) :
    d.frame.names.input binder = d.capture binder := by
  simp [AuthoredBodyFrame393.names,DefaultDeclaration.frame,GeneralDeclarativeFrameReadback325.sourceNames,
    GeneralDeclarativeProducedNames325.table,Declaration.outputNames,d.noOutputBinders]

def DefaultDeclaration.sourceHead {p r} (d : DefaultDeclaration p r) :
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

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
