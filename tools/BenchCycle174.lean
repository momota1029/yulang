import Yulang.GeneralDictionaryAgreedUniform174

/-! A bounded performance smoke test, not a proof or declaration-validity test.
These synthetic Registry values deliberately do not assert Checked; only the
independent role graph certificate is exercised. No language verdict follows.
Duplicate outgoing edges expose recomputation in the current height search. -/
open Yulang GeneralDeclarations GeneralDictionaryAgreedUniform174

def chain174 (length : Nat) (duplicate : Bool) : Registry :=
  { GeneralDeclarationExamples.registry with
    declarations := (List.range length).map fun i =>
      { GeneralDeclarationExamples.display with
        id := i + 100
        role := i + 10
        requirements :=
          let clause := { GeneralDeclarationExamples.displayChild with role := i + 11 }
          if duplicate then [clause, clause] else [clause] } }

def benchmark174 (length : Nat) (duplicate : Bool) : IO Unit := do
  let started ← IO.monoMsNow
  let accepted := certify (chain174 length duplicate)
  IO.println s!"length={length} duplicate={duplicate} certified={accepted}"
  let ended ← IO.monoMsNow
  IO.println s!"elapsed_ms={ended - started}"

#eval benchmark174 4 false
#eval benchmark174 4 true
#eval benchmark174 8 false
#eval benchmark174 8 true
#eval benchmark174 12 false
#eval benchmark174 12 true
