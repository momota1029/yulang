import Yulang.GeneralSourceRoleCstKnownOnSuccess296

open Yulang
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstCatalogControl296
  (binder constructor justRole irrelevant duplicated conflicting absentOutput)
open GeneralSourceRoleCstCatalogTrace296 (Issue)
open GeneralSourceRoleCstCatalogExport296 (run Failure Exported)
open GeneralSourceRoleCstSelectedControl295 (both first second packet)
open GeneralSourceRoleCstNamingPacketFixture295 (binderTrace ctorTrace)
open GeneralSourceRoleCstIssuedScope296 (accept Error)
open GeneralSourceRoleCstIssuePacket296 (issue)
open GeneralSourceRoleCstIssueControl296 (noDiagnosticObservation)
open GeneralSourceRoleCstRequiredControl295 (retained permitted)
open GeneralSourceMetadataRoles291 (roleTable)

def hasFailure (why : Failure) : Except Failure Exported → Bool
  | .error got => decide (got = why)
  | _ => false

def stampedError (why : Error) : Except Error Exported → Bool
  | .error e => decide (e = why)
  | _ => false

def main : IO UInt32 := do
  let onLeft := fun c => run .selectedBranch 5 both 71 first (packet first) c 2
  let onRight := fun c => run .selectedBranch 5 both 71 second (packet second) c 2
  let tests : List (String × Except Failure Exported × Failure) := [
    ("unobserved role",onLeft [],.evidence (.missing (.role "Index"))),
    ("observed absence of role",onLeft [(.role "Index",none)],.oldExport),
    ("unobserved output",onLeft justRole,.evidence (.missing (.output 2 "value"))),
    ("constructor namespace cannot stand in for the output name",
      onLeft (justRole ++ [(.constructor "value",some 0)]),.evidence (.missing (.output 2 "value"))),
    ("same spelling in a different role is a different output",
      onLeft (justRole ++ [(.output 3 "value",some 0)]),.evidence (.missing (.output 2 "value"))),
    ("observed absence of output",onLeft absentOutput,.oldExport),
    ("equivalent duplicate is still duplicate raw evidence",onLeft duplicated,.evidence (.ambiguous (.output 2 "value"))),
    ("contradictory rows",onLeft conflicting,.evidence (.ambiguous (.output 2 "value"))),
    ("unobserved demanded constructor",onRight binder,.evidence (.missing (.constructor "char"))),
    ("observed absence of constructor",onRight (binder ++ [(.constructor "char",none)]),.oldExport)
  ]
  for (name,actual,want) in tests do
    unless hasFailure want actual do
      IO.eprintln s!"FAIL {name}"
      return 1
    IO.println s!"PASS {name}"
  let .ok old := onLeft irrelevant.reverse | return 1
  let .ok other := onRight constructor.reverse | return 1
  unless old.trace == binderTrace && other.trace == ctorTrace do return 1
  let .ok stamped := issue .selectedBranch 5 both 71 first (41 : Nat) (packet first) irrelevant 2 | return 1
  unless stamped.packet.catalog == binder do return 1
  let .ok replay := accept stamped.packet both 5 71 first .selectedBranch 41 (packet first) 2 | return 1
  unless replay.trace == binderTrace do return 1
  unless stampedError .mismatchedScope
    (accept stamped.packet both 5 71 first .selectedBranch 42 (packet first) 2) do return 1
  unless stampedError .mismatchedScope
    (accept stamped.packet both 5 71 first .selectedBranch 41 (packet first) 3) do return 1
  unless stampedError .mismatchedScope
    (accept stamped.packet both 5 71 second .selectedBranch 41 (packet second) 2) do return 1
  unless stampedError (.selected .selection)
    (accept stamped.packet both 5 71 first .selectedBranch 41 noDiagnosticObservation 2) do return 1
  let .ok required := run .selectedBranch 5 retained 71 first permitted binder 2 | return 1
  let some none := (roleTable required.table 2).assoc 0 | return 1
  unless required.trace == binderTrace do return 1
  IO.println "PASS required output has no default term but its name has a present ID."
  IO.println "PASS reordered catalog yields unchanged ordered trace, unrelated conflicting key ignored."
  IO.println "PASS exact issued footprint replays; altered revision, fallback or address and absent fresh recovery observation deny replay."
  IO.println "Synthetic cases use Lean values; scope/epoch comparisons are not authentication."
  return 0
