import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeWitnessHeader349
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

namespace Yulang.C437NativeFixture
open GeneralDeclarativeWitnessConstructorModes357
open GeneralDeclarations (Declaration Equation)
open GeneralSourceMetadataRows291 (Row)
open GeneralSourceMetadataBareBundle291 (InputBundle)

def seedBody : Equation := ⟨80,6,.app 20 [.var 8]⟩
def seed : Declaration := ⟨701,11,[.app 20 [.var 8]],[],[seedBody],[]⟩
def observe : Declaration := ⟨702,22,[.app 20 [.var 9]],[],[],[]⟩
def bundle (snapshotClass : GeneralSourceMetadataRows291.Class) (duplicate := false) : InputBundle :=
  let originals : List Row := [⟨20,some ⟨[.type],20⟩,.unclassified⟩]
  let snapshot : List Row := [⟨20,some ⟨[.type],20⟩,snapshotClass⟩]
  ⟨⟨.absent,originals⟩,⟨.absent,snapshot⟩,
     ⟨1,[⟨11,1,[(6,none)]⟩,⟨22,1,[]⟩]⟩, if duplicate then [seed,observe,observe] else [seed,observe]⟩

def env? (data : InputBundle) : Option Environment := do
  let source := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← GeneralDeclarativeWitnessSparseVariance357.compile source
  let book ← GeneralSourceMetadataBareBundle291.compile data
  return ⟨3,2,0,source,graph,book⟩

def native : Environment := (env? (bundle .unclassified)).get (by decide +kernel)
def priorInvariant : Environment := (env? (bundle .invariant)).get (by decide +kernel)
def duplicateDecl : Environment := (env? (bundle .unclassified true)).get (by decide +kernel)

def legacyExplicit (e : Environment) : Bool :=
  GeneralSourceMetadataDeclarations291.explicitCheck
    (GeneralSourceMetadataBundle291.registry e.source)
    (GeneralSourceMetadataRows291.interpretation e.source.snapshot)

namespace Tests

open GeneralDeclarativeI65.CompletedNativeHeader437

theorem source_body_replays_covariant437 :
    ((readUse native 20 1).map (fun u => match u.mode with | .declared ps => some ps | _ => none)) =
      some (some [⟨.value,.covariant⟩]) := by decide +kernel

theorem genuine_native_header_not_legacy437 :
    checkHeader native = true ∧ legacyExplicit native = false := by decide +kernel

theorem invariant_flag_cannot_stand_in_for_declaration437 :
    checkHeader priorInvariant = false ∧ (readUse priorInvariant 20 1).isSome = false := by decide +kernel

theorem duplicate_declaration_does_not_pass437 : checkHeader duplicateDecl = false := by decide +kernel

#print axioms checkedDecl
#print axioms checkedHeader
#print axioms source_body_replays_covariant437
#print axioms genuine_native_header_not_legacy437
#print axioms invariant_flag_cannot_stand_in_for_declaration437
#print axioms duplicate_declaration_does_not_pass437

end Tests
end Yulang.C437NativeFixture
