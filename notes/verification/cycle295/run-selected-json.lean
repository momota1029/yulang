import Yulang.GeneralSourceRoleCstSelectedJson295

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read encode)
open GeneralSourceRoleCstWire293 (Wire decode)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary captureAt)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstSelectedOutcome295 (Error)
open GeneralSourceRoleCstSelectedJson295 (fromText fromValue)
open GeneralSourceRoleCstSelectedControl295 (first second packet both naming)
open GeneralSourceRoleCstNamingControl295 (shiftedCtor shiftedOutput irrelevant)
open GeneralSourceRoleCstNamingPacketFixture295 (pinnedFirst pinnedSecond binderTrace)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles (Term)

def oldBinder (t : RoleSource) : Bool :=
  match (roleTable t 2).assoc 0 with
  | some (some (.var 1)) => true
  | _ => false

def oldCtor (t : RoleSource) : Bool :=
  match (roleTable t 2).assoc 0 with
  | some (some (.app 3 [])) => true
  | _ => false

def failsAs (e : Error) : Except Error RoleSource → Bool
  | .error got => decide (got = e)
  | .ok _ => false

def goldenEnv (_ : Nat) : Environment :=
  ⟨fun n => if n = "a" then some 7 else none,fun _ _ => none,fun _ => none⟩

def unknownEnv (_ : Nat) : Environment := ⟨fun _ => none,fun _ _ => none,fun _ => none⟩

def main (args : List String) : IO UInt32 := do
  let [filename] := args | return 2
  let serialized ← IO.FS.readFile filename
  let .ok j := Json.parse serialized | return 2
  let some w := read 64 j | return 2
  let a : Address Nat := ⟨17,[0]⟩
  let selection : Boundary Nat Nat := ⟨11,⟨a,.selectedBranch,⟨w,.reported 17 [.errorGroupRange ⟨49,58⟩]⟩⟩⟩
  let named := (⟨selection,[(.role "a",some 7)]⟩ : FiniteBoundary Nat Nat)
  let .ok t := fromText 64 serialized .selectedBranch 11 17 a named goldenEnv 1 | return 1
  let [r] := t.rows | return 1
  -- Wire structure is fixed, not the enclosing JSON whitespace.
  let .ok spaced := fromText 64 ("  \n" ++ serialized ++ "\n  ") .selectedBranch 11 17 a named goldenEnv 1 | return 1
  unless spaced.rows.length == 1 do return 1
  unless r.role == 7 && r.arity == 1 && r.outputs.isEmpty do return 1
  let .error (.badJson _) := fromText 64 "{broken" .selectedBranch 11 17 a named goldenEnv 1 | return 1
  unless failsAs .schemaOrDepth (fromText 64 "{}" .selectedBranch 11 17 a named goldenEnv 1) do return 1
  unless failsAs .schemaOrDepth (fromText 1 serialized .selectedBranch 11 17 a named goldenEnv 1) do return 1
  unless failsAs .selectionOrRecovery
      (fromText 64 serialized .selectedBranch 11 17 ⟨17,[1]⟩ named goldenEnv 1) do return 1
  unless failsAs .namingMismatch (fromText 64 serialized .selectedBranch 11 17 a named unknownEnv 1) do return 1
  unless failsAs .oldExportRejected
      (fromText 64 serialized .selectedBranch 11 17 a ⟨selection,[(.role "a",none)]⟩ unknownEnv 1) do return 1
  let .ok l := fromValue 64 (encode both) .selectedBranch 5 71 first pinnedFirst naming 2 | return 1
  let .ok e := fromValue 64 (encode both) .selectedBranch 5 71 second pinnedSecond naming 2 | return 1
  unless oldBinder l && oldCtor e do return 1
  let .ok same := fromValue 64 (encode both) .selectedBranch 5 71 first pinnedFirst irrelevant 2 | return 1
  unless oldBinder same do return 1
  unless failsAs .selectionOrRecovery
      (fromValue 64 (encode both) .selectedBranch 5 71 second pinnedFirst naming 2) do return 1
  unless failsAs .namingMismatch
      (fromValue 64 (encode both) .selectedBranch 5 71 first pinnedFirst shiftedOutput 2) do return 1
  unless failsAs .namingMismatch
      (fromValue 64 (encode both) .selectedBranch 5 71 second pinnedSecond shiftedCtor 2) do return 1
  let .node "Root" cs := both | return 1
  let modified : Wire := .node "Root" (cs ++ [.token "Newline" "\n"])
  unless failsAs .selectionOrRecovery
      (fromValue 64 (encode modified) .selectedBranch 5 71 first pinnedFirst naming 2) do return 1
  unless failsAs .selectionOrRecovery
      (fromValue 64 (encode both) .selectedBranch 5 72 first pinnedFirst naming 2) do return 1
  let unavailable := ({selection with selected := {selection.selected with receipt :=
    ⟨w,.absent⟩}} : Boundary Nat Nat)
  unless failsAs .selectionOrRecovery
      (fromText 64 serialized .selectedBranch 11 17 a ⟨unavailable,[(.role "a",some 7)]⟩ goldenEnv 1) do return 1
  IO.println "Archived JSON -> selected role a at [0] -> caller-named row #7 (arity 1), no associated outputs."
  IO.println "Malformed JSON, depth/schema failure, retargeting, changed naming, and old exporter failure stayed distinct."
  IO.println "Synthetic paired roles: chosen [0] produced the binder default; chosen [2] produced char."
  IO.println "First seal cannot retarget [2]; changed output or used constructor rejected, irrelevant name permitted."
  IO.println "A changed retained wire, a foreign brand, and an absent diagnostic receipt all deny handoff."
  IO.println "Reformatting only the JSON envelope preserves the exact retained wire and selected role."
  IO.println "Lean execution over portable CST; no Rust run or authenticated lookup/diagnostic source."
  return 0
