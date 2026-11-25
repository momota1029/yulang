import Yulang.GeneralDeclarativeI65I74RoleDefaultSource420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open GeneralDictionaryAssociatedProvenance (Body)
open ExplicitPick419 (Rows pickSyntax inputView RetainedOutput exactlyOneOutput replayOutput one_output_is_zero419 raw_root_safety_on_original_demand419)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open ClosedResidual415 (RowsWire readRows415)

/-- Check the fixed source's explicit declarations by their established
coverage, and all authored defaults by the native-aware typed table.
The legacy default reifier is not a gate for genuine declared constructors. -/
def checkHeader (env : GeneralDeclarativeWitnessConstructorModes357.Environment) : Bool :=
  GeneralSourceMetadataRoles291.check env.source.roles &&
    GeneralSourceMetadataDeclarations291.explicitCheck
      (GeneralSourceMetadataBundle291.registry env.source)
      (GeneralSourceMetadataRows291.interpretation env.source.snapshot) &&
    GeneralDeclarativeWitnessHeader349.checkedRegistry env.source &&
    GeneralDeclarativeWitnessModeCoverage357.check env

theorem checked_default_header420 {env} (ok : checkHeader env = true) :
    GeneralDeclarations.Checked (GeneralSourceMetadataBundle291.registry env.source) ∧
      GeneralDeclarativeWitnessModeCoverage357.Coverage env := by
  obtain ⟨top,modes⟩ := splitAnd ok
  obtain ⟨other,header⟩ := splitAnd top
  obtain ⟨roles,explicit⟩ := splitAnd other
  have checkedRoles := (GeneralSourceMetadataRoles291.check_exact _).mp roles
  have covered := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp explicit
  obtain ⟨keys,checks⟩ := splitAnd header
  exact ⟨⟨of_decide_eq_true keys,fun d h =>
    GeneralDeclarativeWitnessHeader349.decl_checked (covered d h) (List.all_eq_true.mp checks d h)⟩,
    (GeneralDeclarativeWitnessModeCoverage357.check_exact checkedRoles).mp modes⟩

def readDeclaration420 (p : Problem) (r : Rows p) (ordinal : Nat) :
    Option (DefaultDeclaration p r) := do
  let env := p.state.core.current.environment
  let metadata := env.source
  match h : visible p.state.core p.root with
  | [d] =>
    if atOrdinal : (authoredRegistry p.state.core.current).declarations[ordinal]? = some d then
      match roleFact : GeneralSourceMetadataFiniteLookup291.get p.root.demand.role
          (GeneralSourceMetadataRoles291.index metadata.roles) with
      | none => none
      | some role =>
        if header : checkHeader env = true then
          let valid := checked_default_header420 header
          let checked := valid.1
          have atDecl := List.mem_of_getElem? atOrdinal
          let covered := valid.2.1 d atDecl
          let authority := GeneralSourceMetadataRoles291.indexed roleFact
          match head : d.head with
          | [.record label (.var field) (.var tail)] =>
            if shape : label = r.x ∧ field ≠ tail ∧ d.requirements = [] ∧
                d.outputBinders = [] then
              some ⟨d,ordinal,atOrdinal,h,⟨role,authority.1,authority.2⟩,checked,covered,
                field,tail,shape.2.1,by simpa [pickSyntax,shape.1] using head,
                shape.2.2.1,shape.2.2.2⟩
            else none
          | _ => none
        else none
    else none
  | _ => none

theorem read_declaration_uses_the_supplied_ordinal420 {p r pos d}
    (found : readDeclaration420 p r pos = some d) : d.ordinal = pos := by
  dsimp only [readDeclaration420] at found
  repeat' (first | split at found | contradiction)
  cases Option.some.inj found
  rfl

structure DefaultPacket (p : Problem) where
  rows : Rows p
  declaration : DefaultDeclaration p rows
  single : p.root.demand.outputs.length = 1
  retained : RetainedOutput p declaration.frame (exactlyOneOutput p single)
  term : Roles.Term
  actualBody : retained.output.body = .default declaration.decl.role
    p.root.demand.outputs[exactlyOneOutput p single].name term
  targetDifferent : p.root.demand.outputs[exactlyOneOutput p single].target ∉
    [rows.root,rows.intSlot,rows.strSlot,rows.residual]
  rawSafe : ¬ RootCycle p.state p.root

def DefaultPacket.event {p} (a : DefaultPacket p) : Event p.state p.root :=
  ⟨a.declaration.frame,a.declaration.sourceHead,
    fun i => (one_output_is_zero419 p a.single i).symm ▸ a.retained.output⟩

theorem actual_default_never_switches_to_a_where_child420 {p} (a : DefaultPacket p) :
    a.event.kids = [] := by
  simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,
    DefaultPacket.event,DefaultDeclaration.frame,a.declaration.clauseFree]

theorem default_uses_exact_retained_typed_row420 {p} (a : DefaultPacket p) :
    RetainedTypedValueRows403 a.event := by
  intro i
  rw [one_output_is_zero419 p a.single i]
  exact ⟨a.retained.expr,a.retained.code,a.retained.atRow⟩

structure DefaultWire where
  rows : RowsWire
  declaration : Nat
  outputRow : Nat
  rootEscape : ExactEscapeWire

def ownerDefaultTerm : Body → Option Roles.Term
  | .explicit _ => none
  | .default _ _ term => some term

def replayDefault420 (p : Problem) (wire : DefaultWire) : Option (DefaultPacket p) := do
  let r ← readRows415 (inputView p) wire.rows
  if safe : checkExactEscape p.state.core.current.ordinary r.root wire.rootEscape = true then
    let d ← readDeclaration420 p r wire.declaration
    if one : p.root.demand.outputs.length = 1 then
      let i := exactlyOneOutput p one
      let read ← replayOutput p d.frame d.checked i wire.outputRow
      let term ← ownerDefaultTerm read.output.body
      if body : read.output.body = .default d.decl.role p.root.demand.outputs[i].name term then
        if target : p.root.demand.outputs[i].target ∉ [r.root,r.intSlot,r.strSlot,r.residual] then
          pure ⟨r,d,one,read,term,body,target,
            raw_root_safety_on_original_demand419 r (exact_escape_refutes_raw_root_K2410 safe)⟩
        else none
      else none
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
