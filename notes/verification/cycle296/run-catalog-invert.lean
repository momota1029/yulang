import Yulang.GeneralSourceRoleCstTrimCatalog296

open Yulang
open GeneralSourceRoleCstCatalogControl296 (binder constructor irrelevant)
open GeneralSourceRoleCstSelectedControl295 (first second both packet naming actualRead)
open GeneralSourceRoleCstNamingPacketFixture295 (binderTrace ctorTrace)
open GeneralSourceRoleCstCatalogExport296 (run)
open GeneralSourceRoleCstSelectedEvidence296 (extractCatalog)
open GeneralSourceRoleCstSelectedCompile295 (compile)
open GeneralSourceRoleCstRecoveredCatalog296 (recoverCatalog)
open GeneralSourceRoleCstRecoveredControl296
  (repeatedChar compatibleRow conflictingRow compactCatalog binderRole ordinary alternate wronglyPlaced)
open GeneralSourceRoleCstCatalogTrace296 (produce)
open Roles (Term)

def intResult : Option Term → Bool
  | some (.app 0 []) => true
  | _ => false

def charResult : Option Term → Bool
  | some (.app 3 []) => true
  | _ => false

def main : IO UInt32 := do
  let some oldFirst := compile .selectedBranch 5 both 71 first (packet first) naming 2 | return 1
  let some oldSecond := compile .selectedBranch 5 both 71 second (packet second) naming 2 | return 1
  let some c1 := extractCatalog .selectedBranch 5 both 71 first (packet first) oldFirst | return 1
  let some c2 := extractCatalog .selectedBranch 5 both 71 second (packet second) oldSecond | return 1
  unless c1 == binder && c2 == constructor do return 1
  let .ok l := run .selectedBranch 5 both 71 first (packet first) c1 2 | return 1
  let .ok r := run .selectedBranch 5 both 71 second (packet second) c2 2 | return 1
  unless l.trace == binderTrace && r.trace == ctorTrace do return 1
  unless intResult (actualRead l.table) && charResult (actualRead r.table) do return 1
  let .ok oversupplied := run .selectedBranch 5 both 71 first (packet first) irrelevant 2 | return 1
  unless extractCatalog .selectedBranch 5 both 71 first (packet first) oversupplied.table == some binder do return 1
  unless recoverCatalog repeatedChar compatibleRow == some compactCatalog do return 1
  if (recoverCatalog repeatedChar conflictingRow).isSome || (recoverCatalog binderRole wronglyPlaced).isSome then return 1
  let some base := recoverCatalog binderRole ordinary | return 1
  let some different := recoverCatalog binderRole alternate | return 1
  if base == different then return 1
  IO.println "Actual existing Lean assocOf after inversion/replay: selected [0] -> int; selected [2] -> char."
  IO.println "Finite extraction omitted unrelated rows and coalesced two compatible occurrences of one constructor."
  IO.println "Conflicting constructor resolutions and a substituted wrong binder position were rejected."
  IO.println "Two structurally valid different numeric tables remain possible; no authority comes from syntax."
  IO.println "Synthetic wrapped associations, executed in Lean only."
  return 0
