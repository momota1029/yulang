import Yulang.GeneralDeclarativeI65I74ExplicitPickSource419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open ClosedResidual415 (RowsWire readRows415)

def readDeclaration419 (p : Problem) (r : Rows p) (ordinal : Nat) :
    Option (PickDeclaration p r) := do
  let env := p.state.core.current.environment
  let metadata := env.source
  match h : visible p.state.core p.root with
  | [d] =>
    if atOrdinal : (authoredRegistry p.state.core.current).declarations[ordinal]? = some d then
      match roleFact : GeneralSourceMetadataFiniteLookup291.get p.root.demand.role
          (GeneralSourceMetadataRoles291.index metadata.roles) with
      | none => none
      | some role =>
        if header : (GeneralSourceMetadataRoles291.check metadata.roles &&
            GeneralDeclarativeWitnessProblem349.covered metadata &&
            GeneralDeclarativeWitnessHeader349.checkedRegistry metadata &&
            GeneralDeclarativeWitnessModeCoverage357.checkDecl env d) = true then
          let checked := GeneralDeclarativeWitnessHeader349.registry_checked
            ((GeneralDeclarativeWitnessProblem349.covered_iff
              ((GeneralSourceMetadataRoles291.check_exact _).mp (splitAnd (splitAnd (splitAnd header).1).1).1)).mp
              (splitAnd (splitAnd (splitAnd header).1).1).2)
            (splitAnd (splitAnd header).1).2
          let covered := (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp (splitAnd header).2
          let authority := GeneralSourceMetadataRoles291.indexed roleFact
          match head : d.head, written : d.associated with
          | [.record label (.var field) (.var tail)],[eq] =>
            if shape : label = r.x ∧ field ≠ tail ∧ d.requirements = [] ∧
                d.outputBinders = [] ∧ eq.rhs = .var field then
              some ⟨d,ordinal,atOrdinal,h,⟨role,authority.1,authority.2⟩,checked,covered,
                field,tail,shape.2.1,by simpa [pickSyntax,shape.1] using head,
                shape.2.2.1,shape.2.2.2.1,eq,written,shape.2.2.2.2⟩
            else none
          | _,_ => none
        else none
    else none
  | _ => none

structure PickPacket (p : Problem) where
  rows : Rows p
  declaration : PickDeclaration p rows
  single : p.root.demand.outputs.length = 1
  retained : RetainedOutput p declaration.frame (exactlyOneOutput p single)
  actualBody : retained.output.body = .explicit declaration.explicit
  fieldCode : retained.expr = .variable rows.intSlot
  targetDifferent : p.root.demand.outputs[exactlyOneOutput p single].target ∉
    [rows.root,rows.intSlot,rows.strSlot,rows.residual]
  rawSafe : ¬ RootCycle p.state p.root

def PickPacket.event {p} (a : PickPacket p) : Event p.state p.root :=
  ⟨a.declaration.frame,a.declaration.sourceHead,
    fun i => (one_output_is_zero419 p a.single i).symm ▸ a.retained.output⟩

theorem actual_pick_never_switches_to_a_where_child419 {p} (a : PickPacket p) :
    a.event.kids = [] := by
  simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,
    PickPacket.event,PickDeclaration.frame,a.declaration.clauseFree]

theorem pick_uses_exact_retained_typed_row419 {p} (a : PickPacket p) :
    RetainedTypedValueRows403 a.event := by
  intro i
  rw [one_output_is_zero419 p a.single i]
  exact ⟨a.retained.expr,a.retained.code,a.retained.atRow⟩

structure PickWire where
  rows : RowsWire
  declaration : Nat
  outputRow : Nat
  rootEscape : ExactEscapeWire

def replayPick419 (p : Problem) (wire : PickWire) : Option (PickPacket p) := do
  let r ← readRows415 (inputView p) wire.rows
  if safe : checkExactEscape p.state.core.current.ordinary r.root wire.rootEscape = true then
    let d ← readDeclaration419 p r wire.declaration
    if one : p.root.demand.outputs.length = 1 then
      let i := exactlyOneOutput p one
      let read ← replayOutput p d.frame d.checked i wire.outputRow
      if body : read.output.body = .explicit d.explicit then
        if code : eqExpr read.expr (.variable r.intSlot) = true then
          if target : p.root.demand.outputs[i].target ∉ [r.root,r.intSlot,r.strSlot,r.residual] then
            pure ⟨r,d,one,read,body,(eq_expr _ _).mp code,target,
              raw_root_safety_on_original_demand419 r (exact_escape_refutes_raw_root_K2410 safe)⟩
          else none
        else none
      else none
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
