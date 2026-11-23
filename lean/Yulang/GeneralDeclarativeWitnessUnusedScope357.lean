import Yulang.GeneralDeclarativeWitnessInheritedFullFixture357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 48000
set_option maxHeartbeats 42000000

namespace Yulang.GeneralDeclarativeWitnessUnusedScope357
open CommonRecursiveNominalIntervals (Endpoint compileInContext)
open GeneralDeclarativeWitnessSparseIntervals357 (compile)
open GeneralDeclarativeWitnessSparseVariance357 (Source lookup)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (catalog)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open CommonDeclaredNominalInspection (Registry)
open PresenceNormalForm (Atom)

def source : Source 1 1 0 := ⟨[⟨43,[(.value,0)]⟩,⟨90,[]⟩],fun _ => .base .int,fun _ => 0⟩

def bundle : InputBundle :=
  let rows := [⟨43,some ⟨[.type],43⟩,.unclassified⟩,⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[]⟩,[]⟩

def prepare : Option Environment := do
  let checked ← GeneralDeclarativeWitnessSparseVariance357.compile source
  let parsed ← GeneralSourceMetadataBareBundle291.compile bundle
  pure ⟨1,1,0,source,checked,parsed⟩

def table : Registry :=
  (List.range 91).map (fun key => if key = 43 then [⟨.value,.unused⟩] else [])

def wrapping (term : Endpoint Nat) : Endpoint Nat :=
  .nominal 43 [.inl (.point term)]

def run (left right : Endpoint Nat) : Option (List (Atom Nat)) :=
  prepare.bind fun e => (compile e table true left right).map (fun a => a.rows)

theorem really_unused : (GeneralDeclarativeWitnessSparseVariance357.compile source).bind
    (fun c => lookup c 43) = some [⟨.value,.unused⟩] := by decide +kernel

theorem used_syntax_but_no_obligations :
    run (wrapping (.nominal 90 []))
      (wrapping (.ordinary (.var 8))) = some [] := by decide +kernel

theorem does_not_offer_missing_under_unused :
    run (wrapping (.nominal 21 []))
      (wrapping (.ordinary (.var 8))) = none := by decide +kernel

theorem wrong_unused_kind_still_fails :
    run (.nominal 43 [.inr (.point (.var 7))]) (.nominal 43 [.inr (.point (.var 8))]) = none := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessUnusedScope357
