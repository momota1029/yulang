import Yulang.GeneralDeclarativeI65I74ClosedResidualRows415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open CommonRoleOutermostResolver (All₂)

structure ExactCandidate (s : I72.State) (q : I72.Request) where
  decl : Declaration
  ordinal : Nat
  authored : (authoredRegistry s.core.current).declarations[ordinal]? = some decl
  visibleOne : visible s.core q = [decl]
  role : ∃ r ∈ s.core.current.environment.source.roles.rows, r.role = q.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid s.core.current.environment.source.roles
  covered : DeclarationCovered s.core.current.environment decl
  signature : decl.Signature (authoredRegistry s.core.current).roles
  noBinders : decl.outputBinders = []
  noAssociated : decl.associated = []

def query415 (q : I72.Request) (role residual : Nat) : I72.Request :=
  ⟨q.occurrence ++ [0],⟨role,[point residual],[]⟩⟩

def childHead415 (label empty payloadBinder : Nat) : Pattern :=
  .record label (.var payloadBinder) (.app empty [])

structure ClosedParent {s q} (a : ClosedRows s q) where
  candidate : ExactCandidate s q
  intName : Nat
  binder : Nat
  childRole : Nat
  clauseID : Nat
  roleDifferent : childRole ≠ q.demand.role
  literal : candidate.decl.head = [OpenTail414.openHead a.x intName binder]
  clause : candidate.decl.requirements = [OpenTail414.tailRequirement childRole binder clauseID]
  mappedInt : application (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) intName [] =
      some (.primitive (.scalar .int) [])
  intSafe : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) a.intSlot

structure ClosedChild {s q} {a : ClosedRows s q} (p : ClosedParent a) where
  candidate : ExactCandidate s (query415 q p.childRole a.residual)
  emptyName : Nat
  binder : Nat
  literal : candidate.decl.head = [childHead415 a.y emptyName binder]
  noWhere : candidate.decl.requirements = []
  mappedEmpty : application (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) emptyName [] =
      some (.primitive .emptyRecord [])
  strSafe : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) a.strSlot

def pointCapture415 (b name : Nat) (n : Nat) : Capture :=
  if n = b then point name else emptyCapture403

def ClosedParent.head {s q} {a : ClosedRows s q} (p : ClosedParent a) :
    SourceHead s.core q p.candidate.decl := by
  let capture := pointCapture415 p.binder a.residual
  let code : Expr := .record a.x (.primitive (.scalar .int) []) (.variable p.binder)
  have compiled : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (OpenTail414.openHead a.x p.intName p.binder) = some code := by
    simp [OpenTail414.openHead,code,translate,translateMany,p.mappedInt]
  refine .ordered capture ?_
  rw [a.requested,p.literal]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,code,compiled,.direct (.structural ?_)⟩) .nil
  refine .record a.retainedSplit (.primitive (n := 0) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) a.integer (fun i => Fin.elim0 i)) (.capture ?_ ?_)
  · simp [capture,pointCapture415,point,GeneralDeclarativeHead320.byMode]
    exact .refl _
  · simp [capture,pointCapture415,point,GeneralDeclarativeHead320.byMode]
    exact .refl _

def ClosedChild.head {s q} {a : ClosedRows s q} {p : ClosedParent a} (c : ClosedChild p) :
    SourceHead s.core (query415 q p.childRole a.residual) c.candidate.decl := by
  let capture := pointCapture415 c.binder a.strSlot
  let code : Expr := .record a.y (.variable c.binder) (.primitive .emptyRecord [])
  have compiled : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (childHead415 a.y c.emptyName c.binder) = some code := by
    simp [childHead415,code,translate,translateMany,c.mappedEmpty]
  refine .ordered capture ?_
  rw [c.literal]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,code,compiled,.direct (.whole ?_)⟩) .nil
  simpa [code,query415,capture,pointCapture415,point,GeneralDeclarativeHead320.byMode,
    GeneralDeclarativeSubstitution320.logical,GeneralDeclarativeSubstitution320.logicals,residualExpr]
    using a.retainedResidual

def ExactCandidate.frame {s q} (d : ExactCandidate s q) (f : Nat → Capture) :
    AuthoredBodyFrame393 s.core q :=
  ⟨d.ordinal,d.decl,d.authored,by simp [d.visibleOne],unusedPlacement403,f⟩

theorem candidate_has_exact_input415 {s q} (d : ExactCandidate s q) (f : Nat → Capture) (n : Nat) :
    (d.frame f).names.input n = f n := by
  simp [AuthoredBodyFrame393.names,ExactCandidate.frame,GeneralDeclarativeFrameReadback325.sourceNames,GeneralDeclarativeProducedNames325.table,
    Declaration.outputNames,d.noBinders]

def ClosedParent.event {s q} {a : ClosedRows s q} (p : ClosedParent a) : Event s q :=
  ⟨p.candidate.frame (pointCapture415 p.binder a.residual),p.head,fun i => by
    have h := i.isLt
    simp [a.noOutputs] at h⟩

def ClosedChild.event {s q} {a : ClosedRows s q} {p : ClosedParent a}
    (c : ClosedChild p) : Event s (query415 q p.childRole a.residual) :=
  ⟨c.candidate.frame (pointCapture415 c.binder a.strSlot),c.head,fun i => Fin.elim0 i⟩

theorem parent_emits_actual_residual_child415 {s q} {a : ClosedRows s q} (p : ClosedParent a) :
    p.event.kids = [query415 q p.childRole a.residual] := by
  let cl := OpenTail414.tailRequirement p.childRole p.binder p.clauseID
  have exactDemand : (p.event.frame.whereFor cl).demand = (query415 q p.childRole a.residual).demand := by
    have lit := literal_variable_where_uses_actual_names403 p.event.frame
      (c := cl) (binders := [p.binder]) rfl rfl
    rw [lit]
    change _ = _
    simp [query415,cl,OpenTail414.tailRequirement,ClosedParent.event,
      candidate_has_exact_input415,pointCapture415]
  unfold Event.kids frameWhereKids400 children AuthoredBodyFrame393.clauses
  change _ = _
  simp [ClosedParent.event,ExactCandidate.frame,p.clause]
  change (⟨q.occurrence ++ [0],(p.event.frame.whereFor cl).demand⟩ : I72.Request) = _
  rw [exactDemand]
  rfl

theorem residual_leaf_has_no_child415 {s q} {a : ClosedRows s q} {p : ClosedParent a} (c : ClosedChild p) :
    c.event.kids = [] := by
  simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,ClosedChild.event,
    ExactCandidate.frame,c.noWhere]

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
