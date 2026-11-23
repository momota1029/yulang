import Yulang.GeneralDeclarativeWitnessModeCoverage357
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCoverageFixture357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use Mode readUse)
open GeneralDeclarativeWitnessModeCoverage357 (check Coverage check_exact)
open GeneralDeclarativeWitnessVarianceFixtures357 (source)
open GeneralSourceMetadataRows291 (Row Source)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)

def catalog : List Row :=
  [⟨18,some ⟨[.type,.type],18⟩,.primitive .pair⟩,
   ⟨55,some ⟨[.type],55⟩,.invariant⟩,
   ⟨20,some ⟨[.type],20⟩,.unclassified⟩,
   ⟨42,some ⟨[.type],42⟩,.unclassified⟩,
   ⟨90,some ⟨[],90⟩,.unclassified⟩]

def written : Declaration :=
  ⟨71,5,[.app 20 [.var 0]],
    [⟨81,6,[.app 42 [.var 0]],[⟨91,1,.app 55 [.var 0]⟩]⟩],
    [⟨92,0,.app 18 [.var 0,.app 90 []]⟩],[]⟩

def bundle : InputBundle :=
  ⟨⟨.absent,catalog⟩,⟨.absent,catalog⟩,
    ⟨0,[⟨5,1,[(0,none),(1,some (.app 90 []))]⟩,⟨6,1,[(1,none)]⟩]⟩,
    [written]⟩

def prepare (b : InputBundle := bundle) : Option Environment := do
  let checked ← GeneralDeclarativeWitnessSparseVariance357.compile source
  let resolved ← compile b
  pure ⟨3,2,0,source,checked,resolved⟩

def test (b : InputBundle := bundle) : Bool := ((prepare b).map check).getD false

theorem whole_declaration_and_default : test = true := by decide +kernel

def usedPrim : Bool := (prepare.map fun e => ((readUse e 18 2).map fun u =>
  match u.mode with | .primitive .pair => true | _ => false).getD false).getD false

def usedInvariant : Bool := (prepare.map fun e => ((readUse e 55 1).map fun u =>
  match u.mode with | .invariant => true | _ => false).getD false).getD false

theorem primitive_exactly_primitive : usedPrim = true := by decide +kernel
theorem invariant_exactly_invariant : usedInvariant = true := by decide +kernel

theorem no_missing_default_ctor :
    test {bundle with roles := ⟨0,[⟨5,1,[(1,some (.app 21 []))]⟩]⟩} = false := by decide +kernel

theorem no_untrusted_nullary_fallback :
    test {bundle with snapshot := {bundle.snapshot with fallback := .identityEmptyLayout}} = false := by decide +kernel

theorem no_snapshot_kind_drift :
    test {bundle with snapshot := {bundle.snapshot with rows :=
      (catalog.map (fun row => if row.key = 42 then {row with ctor := some ⟨[.row],42⟩} else row))}} = false := by
  decide +kernel

theorem no_forged_invariant_on_covariant :
    test {bundle with snapshot := {bundle.snapshot with rows :=
      (catalog.map (fun row => if row.key = 20 then {row with classification := .invariant} else row))}} = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessCoverageFixture357
