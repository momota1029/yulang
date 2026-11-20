import Yulang.GeneralSourceRoleCstOutcomePrecise295

open Yulang
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWireFixture293 (ws indent ident sigil rawRequired rawMethod)
open GeneralSourceRoleCstSelectedControl295 (rawWrapped rawAssoc first naming)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedJson295 (fromValue)
open GeneralSourceRoleCstSelectedOutcome295 (Error)
open GeneralSourceRoleCstJson293 (encode)
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (roleTable RoleSource)
open Roles (Term)

inductive Want where
  | positional (i : Nat)
  | constant (i : Nat)
  | required
  | rejects (error : Error)

structure Case where
  title : String
  role : Wire
  env : Nat → Environment
  receipt : Trace
  want : Want

def roleWithTypes (members : List Wire) : Wire :=
  match rawWrapped (sigil "'key") with
  | .node tag children => .node tag (children.take 6 ++ [.node "IndentedStatementBlock"
    (members.flatMap (fun t => [indent,.node "Statement" [t]]) ++ [indent,.node "Statement" [rawMethod]])])
  | x => x

def aliasType : Wire :=
  .node "TypeDeclaration" [.token "TypeKw" "type",ws,ident "alias",ws,.token "Equals" "=",ws,
    .node "TypeExpression" [sigil "'key"]]

def aliasEnv (_ : Nat) : Environment :=
  let old := naming 5
  { old with output := fun role name =>
      if role = 2 ∧ name = "alias" then some 0 else old.output role name }

def noRole (_ : Nat) : Environment := ⟨fun _ => none,fun _ _ => none,fun _ => none⟩

def repeatedBinder : Wire :=
  match rawWrapped (sigil "'key") with
  | .node tag children =>
    let arg := .node "TypeApplyArgument" [ws,.node "TypeExpression" [sigil "'key"]]
    .node tag (children.take 4 ++ [.node "TypeExpression" [ident "Index",arg,arg]] ++ children.drop 5)
  | x => x

def exactName : Trace := [(.role "Index",some 2),(.output 2 "value",some 0)]
def declarationCases : List Case := [
  ⟨"second declared binder", rawWrapped (sigil "'key"), naming, exactName, .positional 1⟩,
  ⟨"first declared binder", rawWrapped (sigil "'container"), naming, exactName, .positional 0⟩,
  ⟨"resolved zero-argument constructor", rawWrapped (ident "char"), naming,
    exactName ++ [(.constructor "char",some 3)], .constant 3⟩,
  ⟨"requires output but has no default", roleWithTypes [rawRequired], naming, exactName, .required⟩,
  ⟨"unbound RHS binder",rawWrapped (sigil "'unknown"),naming,exactName,.rejects .oldExportRejected⟩,
  ⟨"unknown RHS constructor",rawWrapped (ident "NotResolved"),naming,
    exactName ++ [(.constructor "NotResolved",none)],.rejects .oldExportRejected⟩,
  ⟨"missing semantic role name",rawWrapped (sigil "'key"),noRole,
    [(.role "Index",none)],.rejects .oldExportRejected⟩,
  ⟨"duplicate output IDs despite exact-name receipt",roleWithTypes [rawAssoc (sigil "'key"),aliasType],
    aliasEnv,exactName ++ [(.output 2 "alias",some 0)],.rejects .oldExportRejected⟩,
  ⟨"duplicate binders despite exact-name receipt",repeatedBinder,naming,exactName,.rejects .oldExportRejected⟩,
  ⟨"unsupported clean integer RHS",rawWrapped (.token "Integer" "4"),naming,exactName,
    .rejects .selectionOrRecovery⟩,
  ⟨"explicit Missing node RHS",rawWrapped (.node "Missing" []),naming,exactName,
    .rejects .selectionOrRecovery⟩,
  ⟨"stale ordered naming receipt",rawWrapped (sigil "'key"),naming,exactName.reverse,
    .rejects .namingMismatch⟩]

def verifiedCase (c : Case) : Bool :=
  let w := Wire.node "Root" [c.role]
  let sealed : FiniteBoundary Nat Nat :=
    ⟨⟨5,⟨first,.selectedBranch,⟨w,.reported 71 []⟩⟩⟩,c.receipt⟩
  let result := fromValue 64 (encode w) .selectedBranch 5 71 first sealed c.env 2
  match c.want,result with
  | .positional n,.ok t => match (roleTable t 2).assoc 0 with
    | some (some (.var i)) => i == n
    | _ => false
  | .constant n,.ok t => match (roleTable t 2).assoc 0 with
    | some (some (.app i [])) => i == n
    | _ => false
  | .required,.ok t => match (roleTable t 2).assoc 0 with
    | some none => true
    | _ => false
  | .rejects e,.error got => decide (e = got)
  | _,_ => false

def main : IO UInt32 := do
  for c in declarationCases do
    unless verifiedCase c do
      IO.eprintln s!"unexpected classification: {c.title}"
      return 1
    IO.println s!"PASS {c.title}"
  IO.println "Synthetic portable wire inputs only: exact receipt evidence does not manufacture names or valid rows."
  return 0
