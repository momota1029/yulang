import Yulang.GeneralDeclarativeI65I74ClosedResidualRule415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (application)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataFiniteLookup291 (get)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

def readCandidate415 (s : I72.State) (q : I72.Request) (j : Nat) :
    Option (ExactCandidate s q) := do
  let cur := s.core.current
  let roles := cur.environment.source.roles
  if valid : GeneralSourceMetadataRoles291.check roles = true then
    match original : get q.demand.role (GeneralSourceMetadataRoles291.index roles) with
    | none => none
    | some r =>
      match whole : visible s.core q with
      | [d] =>
        if atIndex : (authoredRegistry cur).declarations[j]? = some d ∧
            ((authoredRegistry cur).declarations.map Declaration.id).Nodup then
          if header : (GeneralDeclarativeWitnessModeCoverage357.checkDecl cur.environment d &&
               RecordK2412.header412 cur d) = true then
            if noBodies : d.outputBinders = [] ∧ d.associated = [] then
              let found := GeneralSourceMetadataRoles291.indexed original
              let signature := GeneralDeclarativeWitnessSignature349.checked_signature
                (splitAnd (splitAnd (splitAnd header).2).1).1
              some ⟨d,j,atIndex.1,atIndex.2,whole,⟨r,found.1,found.2⟩,
                (GeneralSourceMetadataRoles291.check_exact _).mp valid,
                (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp (splitAnd header).1,
                signature,noBodies.1,noBodies.2⟩
            else none
          else none
        else none
      | _ => none
  else none

def readParent415 {s q} (a : ClosedRows s q) (j : Nat) (fieldGate : ExactEscapeWire) :
    Option (ClosedParent a) := do
  let c ← readCandidate415 s q j
  let cur := s.core.current
  if safe : checkExactEscape cur.ordinary a.intSlot fieldGate = true then
    match head : c.decl.head, req : c.decl.requirements with
    | [.record label (.app intName []) (.var binder)], [clause] =>
      if exact : label = a.x ∧ clause.role ≠ q.demand.role ∧
          clause = OpenTail414.tailRequirement clause.role binder clause.id then
        match intAt : application (authoredRegistry cur).constructors
              (interpretation cur.environment.source.snapshot) intName [] with
        | some (.primitive (.scalar .int) []) =>
          some ⟨c,intName,binder,clause.role,clause.id,exact.2.1,
            by simpa [OpenTail414.openHead,exact.1] using head,
            req.trans (congrArg (fun x => [x]) exact.2.2),intAt,
            exact_escape_refutes_raw_root_K2410 safe⟩
        | _ => none
      else none
    | _,_ => none
  else none

def readChild415 {s q} {a : ClosedRows s q} (p : ClosedParent a) (j : Nat)
    (fieldGate : ExactEscapeWire) : Option (ClosedChild p) := do
  let c ← readCandidate415 s (query415 q p.childRole a.residual) j
  let cur := s.core.current
  if safe : checkExactEscape cur.ordinary a.strSlot fieldGate = true then
    if noWhere : c.decl.requirements = [] then
      match head : c.decl.head with
      | [.record label (.var binder) (.app emptyName [])] =>
        if same : label = a.y then
          match emptyAt : application (authoredRegistry cur).constructors
              (interpretation cur.environment.source.snapshot) emptyName [] with
          | some (.primitive .emptyRecord []) =>
            some ⟨c,emptyName,binder,by simpa [childHead415,same] using head,noWhere,emptyAt,
                exact_escape_refutes_raw_root_K2410 safe⟩
          | _ => none
        else none
      | _ => none
    else none
  else none

structure ClosedWire where
  rows : RowsWire
  parentOrdinal : Nat
  childOrdinal : Nat
  rootEscape : ExactEscapeWire
  intEscape : ExactEscapeWire
  childEscape : ExactEscapeWire
  strEscape : ExactEscapeWire

structure VerifiedClosed (p : Problem) where
  rows : ClosedRows p.state p.root
  parent : ClosedParent rows
  child : ClosedChild parent
  rootSafe : ¬ RootCycle p.state p.root
  childSafe : ¬ RootCycle p.state (query415 p.root parent.childRole rows.residual)

def replayClosed415 (p : Problem) (w : ClosedWire) : Option (VerifiedClosed p) := do
  let a ← readRows415 p w.rows
  let cur := p.state.core.current
  if root : checkExactEscape cur.ordinary a.root w.rootEscape = true then
    if sub : checkExactEscape cur.ordinary a.residual w.childEscape = true then
      let pRead ← readParent415 a w.parentOrdinal w.intEscape
      let c ← readChild415 pRead w.childOrdinal w.strEscape
      have rootSafe : ¬ RootCycle p.state p.root := by
        rintro ⟨x,yes,cycle⟩
        rw [a.requested] at yes
        cases List.mem_singleton.mp yes
        exact exact_escape_refutes_raw_root_K2410 root cycle
      have childSafe : ¬ RootCycle p.state (query415 p.root pRead.childRole a.residual) := by
        rintro ⟨x,yes,cycle⟩
        cases List.mem_singleton.mp yes
        exact exact_escape_refutes_raw_root_K2410 sub cycle
      some ⟨a,pRead,c,rootSafe,childSafe⟩
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
