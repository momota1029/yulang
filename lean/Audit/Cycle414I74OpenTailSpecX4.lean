import Yulang.GeneralDeclarativeI65I74OpenTailEntry414

namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414.SpecX4
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def original : Declaration := ⟨57,7,[openHead 20 9 8],[tailRequirement 7 8 66],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[openRow 0 20 1 2,intRow 1]⟩

def build (rows : List Declaration := [original]) (ordinary : GeneralDeclarativeHead320.State := raw)
    (origins : List GeneralDeclarativeI65.Origin := [⟨0,[22],openTerm 20 1 2⟩]) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨environment,ordinary,[]⟩,[],origins,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : OpenWire := ⟨0,⟨[0,1,2],[0,1,1]⟩⟩
def checkOpt (p : Option Problem) (r : Result := pendingReport) (w : Witness := .openTail wire) :
    Bool := (p.map fun q => check q r w).getD false

theorem actual_X4_keeps_unsolved_tail_pending414 : checkOpt (build) = true := by decide +kernel

def knownTail : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨2,.primitive .emptyRecord []⟩]}
def directAlias : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨2,.variable 1⟩]}
def hiddenBound : GeneralDeclarativeHead320.State :=
  {raw with normal := ⟨[],[(2,1)]⟩}
def decoy : Declaration := {original with id := 58, requirements := []}

theorem X4_does_not_promote_failed_source_reads414 :
    checkOpt (build []) = false ∧ checkOpt (build [decoy]) = false ∧
    checkOpt (build [original,decoy]) = false ∧
    checkOpt (build [original] knownTail) = false ∧
    checkOpt (build [original] directAlias) = false ∧
    checkOpt (build [original] hiddenBound) = false ∧
    checkOpt (build [original] raw [⟨2,[22],.ordinary .emptyRecord⟩,⟨0,[22],openTerm 20 1 2⟩])
      pendingReport (.openTail {wire with original := 1}) = false := by
  decide +kernel

theorem X4_pending_is_not_rejected_or_selected414 :
    checkOpt build Check408.rawReport = false ∧
    checkOpt build (Check408.nullaryReport original) = false ∧
    checkOpt build pendingReport .unsupported = false := by decide +kernel

#eval [checkOpt build,checkOpt (build []),checkOpt (build [decoy]),
   checkOpt (build [original] knownTail),checkOpt (build [original] directAlias),
   checkOpt (build [original] hiddenBound),checkOpt build Check408.rawReport]

#print axioms actual_X4_keeps_unsolved_tail_pending414
#print axioms X4_does_not_promote_failed_source_reads414
#print axioms X4_pending_is_not_rejected_or_selected414
end Yulang.GeneralDeclarativeI65.I72.OpenTail414.SpecX4
