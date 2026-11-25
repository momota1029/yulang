import Yulang.GeneralDeclarativeI65I74ClosedResidualLocation415

namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415.ControlsX4
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty record subtype_refl)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def parent : Declaration := ⟨57,7,[OpenTail414.openHead 20 9 8],
  [OpenTail414.tailRequirement 8 8 66],[],[]⟩
def child : Declaration := ⟨58,8,[childHead415 21 10 13],[],[],[]⟩

def surface (ds : List Declaration) (declared : Bool) : InputBundle :=
  let tags : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩,
                         ⟨10,some ⟨[],10⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,tags⟩,⟨.absent,tags⟩,⟨1,if declared then [⟨7,1,[]⟩,⟨8,1,[]⟩] else []⟩,ds⟩

def rootRow : Equation := ⟨0,wholeExpr 20 1 21 2⟩
def xRow : Equation := OpenTail414.intRow 1
def yRow : Equation := strRow 2
def tailRow : Equation := ⟨3,residualExpr 21 2⟩
def splitRow : Equation := OpenTail414.openRow 0 20 1 3
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,xRow,yRow,tailRow,splitRow]⟩

def build (ds : List Declaration := [parent,child])
    (raw : GeneralDeclarativeHead320.State := ordinary) (declared : Bool := true) : Option Problem := do
  let program ← compile bodies
  let src ← GeneralSourceMetadataBareBundle291.compile (surface ds declared)
  let e : Environment := ⟨0,0,0,bodies,program,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨e,raw,[]⟩,[],[⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : ClosedWire := ⟨⟨0,0,1,2,3,4⟩,0,1,
  ⟨[0,1,2,3],[0,1,1,2]⟩,⟨[0,1,2,3],[2,0,2,2]⟩,
  ⟨[0,1,2,3],[2,2,1,0]⟩,⟨[0,1,2,3],[2,2,0,2]⟩⟩
def report : Result := exactReport parent child
def checkOpt (p : Option Problem := build) (r : Result := report) (w : Witness := .closedRows wire) :
    Bool := (p.map fun data => check data r w).getD false

def originalCoordinates (p : Option Problem) (w : ClosedWire) : Option ResidualLocation := do
  let p ← p
  locate p w

def permutedRows : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [yRow,tailRow,splitRow,xRow,rootRow]}
def permutedWire : ClosedWire :=
  {wire with rows := ⟨0,4,3,0,1,2⟩, parentOrdinal := 1, childOrdinal := 0}

theorem positive_residual_replays_the_original_ordinal_and_child415 :
    checkOpt (build [child,parent] permutedRows) report (.closedRows permutedWire) = true ∧
    originalCoordinates build wire = some ⟨[61],[61,0],0,20,21,3,57,0,58,1,66,8,13⟩ ∧
    originalCoordinates (build [child,parent] permutedRows) permutedWire =
      some ⟨[61],[61,0],0,20,21,3,57,1,58,0,66,8,13⟩ := by decide +kernel

def twoAddresses : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++
    [⟨4,residualExpr 21 2⟩,OpenTail414.openRow 0 20 1 4]}
def duplicateRoleId := {child with id := parent.id}

theorem positive_residual_refuses_same_shape_second_address415 :
    checkOpt (build [parent,child] twoAddresses) = false ∧
    checkOpt (build [parent,child] twoAddresses) report
      (.closedRows {wire with rows := {wire.rows with residualRow := 5, splitRow := 6}}) = false ∧
    checkOpt (build [parent,duplicateRoleId]) (exactReport parent duplicateRoleId) = false := by decide +kernel

def cyclicRoot : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [RecordK2412.recordRow412 0 99 0]}
def rawWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨5,.same,0⟩,[],.same⟩
def actualOldRaw : Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawWire)))))))

def cyclicChild : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [RecordK2412.recordRow412 3 99 3]}

theorem positive_residual_never_replaces_raw_root_or_child_K2415 :
    checkOpt (build [parent,child] cyclicRoot) = false ∧
    checkOpt (build [parent,child] cyclicRoot) Check408.rawReport actualOldRaw = true ∧
    checkOpt (build [parent,child] cyclicChild) = false := by decide +kernel

#eval [checkOpt (build [child,parent] permutedRows) report (.closedRows permutedWire),
  checkOpt (build [parent,child] twoAddresses),checkOpt (build [parent,child] cyclicRoot),
  checkOpt (build [parent,child] cyclicRoot) Check408.rawReport actualOldRaw,
  checkOpt (build [parent,child] cyclicChild)]
#print axioms positive_residual_replays_the_original_ordinal_and_child415
#print axioms positive_residual_refuses_same_shape_second_address415
#print axioms positive_residual_never_replaces_raw_root_or_child_K2415
#print axioms closed_parent_branch_preserves_previous_disjointness415
#print axioms no_prior_child_diagnostic415
#print axioms exact_same_model_split_value415
#print axioms two_replays_cannot_relocate_original_residual415

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415.ControlsX4
