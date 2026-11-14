import Yulang.GeneralDictionaryAgreedTable175

/-! Bounded performance comparison only. Synthetic declarations are not
claimed Checked and these results are not source-language verdicts. -/
open Yulang GeneralDeclarations GeneralDictionaryAgreedUniform174
open GeneralDictionaryAgreedTable175

def chain175 (length : Nat) : Registry :=
  { GeneralDeclarationExamples.registry with
    declarations := (List.range length).map fun i =>
      { GeneralDeclarationExamples.display with
        id := i + 100
        role := i + 10
        requirements :=
          let clause := { GeneralDeclarationExamples.displayChild with role := i + 11 }
          [clause,clause] } }

def sample175 (id length : Nat) : IO Unit := do
  let registry := chain175 length
  let t0 ← IO.monoNanosNow
  let slow := certify registry
  IO.println s!"sample={id} length={length} slow={slow}"
  let t1 ← IO.monoNanosNow
  let fast := certifyTable registry
  IO.println s!"sample={id} length={length} fast={fast}"
  let t2 ← IO.monoNanosNow
  IO.println s!"slow_ns={t1-t0} fast_ns={t2-t1}"

def large175 (length : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let answer := certifyTable (chain175 length)
  IO.println s!"candidate_only length={length} accepted={answer}"
  let t1 ← IO.monoNanosNow
  IO.println s!"candidate_ns={t1-t0}"

#eval sample175 0 12
#eval sample175 1 12
#eval sample175 2 12
#eval sample175 3 12
#eval large175 20
