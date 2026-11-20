import Yulang.GeneralSourceRoleCstJsonEntry293

open Lean (Json)
open Yulang
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstJsonEntry293 (extractText)
open GeneralSourceRoleHeadShape292 (Primary Argument)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleSyntaxBoundary292 (Rhs)

def pathJson (p : List Nat) : Json := .arr (p.map (fun n => Json.num (Lean.JsonNumber.fromNat n))).toArray

def bodyJson : Rhs → Json
  | .absent => .str "required"
  | .binder s => .arr #[.str "binder",.str s]
  | .nullary s => .arr #[.str "unresolvedName",.str s]
  | .recovery => .str "recovery"
  | .unsupported => .str "unsupported"

def memberJson : Address Nat × Child → Json
  | (a,.typeDecl s) => Json.mkObj [("path",pathJson a.path),("name",.str s.spelling),
      ("body",bodyJson s.rhs)]
  | (a,.other) => Json.mkObj [("path",pathJson a.path),("kind",.str "nonType")]
  | (a,.unknown) => Json.mkObj [("path",pathJson a.path),("kind",.str "unknown")]

def getArg : Argument → Option String
  | .binder name => some name
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: run-unresolved-cst.lean file.json [mixed-child-index ...]"
    return 2
  | file :: bits =>
    match bits.mapM String.toNat? with
    | none =>
      IO.eprintln "each path entry must be a natural number"
      return 2
    | some path =>
      let input ← IO.FS.readFile file
      match extractText 64 input () (0 : Nat) ⟨0,path⟩ with
      | .error why =>
        IO.eprintln (reprStr why)
        return 1
      | .ok out =>
        let .simple name := out.head.primary | return 1
        let some parameters := out.head.arguments.mapM getArg | return 1
        IO.println (Json.compress (Json.mkObj [
          ("role",.str name), ("path",pathJson out.atRole.path),
          ("binders",.arr (parameters.map Json.str).toArray),
          ("directMembers",.arr (out.body.map memberJson).toArray)]))
        return 0
