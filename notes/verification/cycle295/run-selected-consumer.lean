import Yulang.GeneralSourceRoleCstSelectedEnd295

open Yulang
open Roles
open Roles.Examples (int str)
open Roles.AssocExamples (char index singletonEnv strImpl str_paterson)
open GeneralSourceRoleCstWire293 (Wire decode spelling)
open GeneralSourceRoleCstWirePaths293 (atWire)
open GeneralSourceRoleCstSpan293 (locate)
open GeneralSourceRoleCstSelectedControl295 (first second both naming rawWrapped actualRead)
open GeneralSourceRoleCstNamingPacketFixture295 (pinnedFirst pinnedSecond)
open GeneralSourceRoleCstSelectedCompile295 (handoff compile)
open GeneralSourceRoleCstNamingPacket295 (checked)
open GeneralSourceRoleCstRequiredControl295 (retained permitted)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

def isInt : Option Term → Bool
  | some (.app 0 []) => true
  | _ => false

def isChar : Option Term → Bool
  | some (.app 3 []) => true
  | _ => false

def traceMember (a : Address Nat) (p : GeneralSourceRoleTrack292.Tracked Nat (Address Nat))
    (expected : String) : IO Bool := do
  unless p.atRole == a do return false
  let some (site,.typeDecl _) := p.body[0]? | return false
  unless site.path == a.path ++ [6,1,0] do return false
  let some root := decode both | return false
  let some (.node "TypeDeclaration" children) := atWire site.path both | return false
  let some (_,roleExtent) := locate a.path root 0 | return false
  let some (_,memberExtent) := locate site.path root 0 | return false
  let rhs := spelling (.node "TypeDeclaration" children)
  unless rhs == expected && roleExtent.low ≤ memberExtent.low &&
      memberExtent.high ≤ roleExtent.high &&
      memberExtent.high - memberExtent.low == rhs.utf8ByteSize do return false
  IO.println s!"{repr a.path}: original TypeDeclaration at {repr site.path}, bytes {memberExtent.low}..{memberExtent.high}: {rhs}"
  return true

def main : IO UInt32 := do
  let some left := checked .selectedBranch 5 both 71 first pinnedFirst naming 2 | return 1
  let some right := checked .selectedBranch 5 both 71 second pinnedSecond naming 2 | return 1
  unless isInt (actualRead left) && isChar (actualRead right) do return 1
  unless isChar (assocOf (singletonEnv strImpl) (roleTable left) str_paterson (index str int) 0) do return 1
  let some x := handoff .selectedBranch 5 both 71 first pinnedFirst.selected | return 1
  let some y := handoff .selectedBranch 5 both 71 second pinnedSecond.selected | return 1
  unless ← traceMember first x "type value = 'key" do return 1
  unless ← traceMember second y "type value = char" do return 1
  let some requirement := compile .selectedBranch 5 retained 71 first permitted naming 2 | return 1
  let some none := (roleTable requirement 2).assoc 0 | return 1
  if (actualRead requirement).isSome then return 1
  IO.println "Existing assocOf: selected [0] omitted -> int; selected [2] omitted -> char."
  IO.println "Existing assocOf explicit override on [0] -> char; required-without-default -> none."
  IO.println "Closed synthetic Wire controls and actual Lean association reader; no Rust parser result."
  return 0
