import Yulang.GeneralSourceRoleCstCatalogEntry296

open Lean (Json)
open Yulang
open GeneralSourceRoleCstCatalogExport296 (Exported)
open GeneralSourceRoleCstCatalogEntry296 (Error fromText)
open GeneralSourceRoleCstCatalogWire296 (decodeCatalog encodeCatalog)
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstSnapshot293 (Address)

def rejects (wanted : Error) : Except Error Exported → Bool
  | .error got => decide (got = wanted)
  | _ => false

def frame (rows : String) : String := "[\"yulang-name-evidence-v1\"," ++ rows ++ "]"

def main (args : List String) : IO UInt32 := do
  let [sourceFile,namesFile] := args | return 2
  let source ← IO.FS.readFile sourceFile
  let names ← IO.FS.readFile namesFile
  let .ok json := Json.parse source | return 2
  let some world := read 64 json | return 2
  let site : Address Nat := ⟨17,[0]⟩
  let sealData : Boundary Nat Nat :=
    ⟨11,⟨site,.selectedBranch,⟨world,.reported 17 [.errorGroupRange ⟨49,58⟩]⟩⟩⟩
  let test : String → Except Error Exported := fun rows =>
    fromText 64 source rows .selectedBranch 11 17 site sealData 1
  let .ok result := test names | return 1
  unless result.trace == [(.role "a",some 7)] do return 1
  unless rejects (.selected (.evidence (.missing (.role "a")))) (test (frame "[]")) do return 1
  unless rejects (.selected .oldExport) (test (frame "[[[\"role\",\"a\"],null]]")) do return 1
  let duplicate := frame "[[[\"role\",\"a\"],7],[[\"role\",\"a\"],8]]"
  let .ok dj := Json.parse duplicate | return 1
  unless decodeCatalog dj == some [(.role "a",some 7),(.role "a",some 8)] do return 1
  unless rejects (.selected (.evidence (.ambiguous (.role "a")))) (test duplicate) do return 1
  for malformed in [
      "[\"yulang-name-evidence-v0\",[]]",
      "{\"a\":7,\"a\":8}",
      frame "[[[\"role\",\"a\"],-1]]",
      frame "[[[\"role\",\"a\"],1.5]]",
      frame "[[[\"role\",\"a\"],\"7\"]]",
      frame "[[[\"role\",\"a\"]]]",
      frame "[[[\"unknown\",\"a\"],7]]",
      frame "[[[\"role\",\"a\"],7],false]"
    ] do
    unless rejects .evidenceSchema (test malformed) do return 1
  let .error (.evidenceText _) := test "{" | return 1
  let .error (.sourceText _) := fromText 64 "{" names .selectedBranch 11 17 site sealData 1 | return 1
  unless rejects .sourceSchemaOrDepth
      (fromText 1 source names .selectedBranch 11 17 site sealData 1) do return 1
  IO.println "Archived selected role consumed external versioned array evidence; no total resolver function supplied."
  IO.println "Missing row, explicit null, and two conflicting rows remain distinct on the wire and in the pipeline."
  IO.println "Eight malformed versions/forms, bad JSON in either channel, and insufficient CST depth rejected."
  IO.println "No Rust parser or semantic catalog authority was executed or inferred."
  return 0
