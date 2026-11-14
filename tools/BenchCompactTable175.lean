import Yulang.GeneralDictionaryAgreedCompactTable175

/-! Bounded paired storage-backend experiment, not a Checked-language test.
The two sizes reuse the preceding duplicated-edge chain fixtures. -/
open Yulang GeneralDeclarations GeneralDictionaryAgreedTable175
open GeneralDictionaryAgreedCompactTable175

def compactChain175 (length : Nat) : Registry :=
  { GeneralDeclarationExamples.registry with
    declarations := (List.range length).map fun i =>
      { GeneralDeclarationExamples.display with
        id := i + 100
        role := i + 10
        requirements :=
          let clause := { GeneralDeclarationExamples.displayChild with role := i + 11 }
          [clause,clause] } }

def compactSample175 (id length : Nat) : IO Unit := do
  let registry := compactChain175 length
  let t0 ← IO.monoNanosNow
  let table := certifyTable registry
  IO.println s!"sample={id} length={length} table={table}"
  let t1 ← IO.monoNanosNow
  let compact := certifyCompact registry
  IO.println s!"sample={id} length={length} compact={compact}"
  let t2 ← IO.monoNanosNow
  IO.println s!"table_ns={t1-t0} compact_ns={t2-t1}"
  IO.println s!"original_entries={GeneralDictionaryAgreedUniform174.roleNodes registry |>.length} compact_entries={compactNodes registry |>.length}"

#eval compactSample175 0 12
#eval compactSample175 1 12
#eval compactSample175 2 12
#eval compactSample175 3 12
#eval compactSample175 0 20
#eval compactSample175 1 20
#eval compactSample175 2 20
#eval compactSample175 3 20
