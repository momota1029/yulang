import Yulang.GeneralDeclarativeI65I74ClosedResidualEntry415

namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415.SpecX4
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

theorem actual_X4_closed_record_selects_through_its_residual415 : checkOpt = true := by decide +kernel

def forged : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,xRow,yRow,⟨3,residualExpr 20 2⟩,splitRow]}
def unretained : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,xRow,yRow,tailRow]}
def wrongTailAddr : ClosedWire := {wire with rows := {wire.rows with residualRow := 0}}
def wrongDecl : ClosedWire := {wire with childOrdinal := 0}
def extra : Declaration := {parent with id := 59}
def wrongClause : Declaration :=
  {parent with requirements := [OpenTail414.tailRequirement 8 8 67], id := 61}

theorem X4_cannot_forge_remainder_or_skip_original_child415 :
    checkOpt (build [parent,child] forged) = false ∧
    checkOpt (build [parent,child] unretained) = false ∧
    checkOpt build report (.closedRows wrongTailAddr) = false ∧
    checkOpt build report (.closedRows wrongDecl) = false ∧
    checkOpt (build [parent]) = false ∧
    checkOpt (build [parent,extra,child]) = false ∧
    checkOpt (build [parent,child] ordinary false) = false ∧
    checkOpt build (Check408.nullaryReport parent) = false ∧
    checkOpt build OpenTail414.pendingReport = false := by decide +kernel

def actualResidualTy : Ty := record 21 (.base .str) .emptyRecord
def actualInputTy : Ty := record 20 (.base .int) actualResidualTy

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then actualInputTy else if n = 1 then .base .int else if n = 2 then .base .str
                  else actualResidualTy),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem actual_closed_X4_state_fits415 {p : Problem} (ready : build = some p) :
    Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [parent,child] true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ seen; cases seen
      · intro _ seen; cases seen
      · intro x found
        change x ∈ [rootRow,xRow,yRow,tailRow,splitRow] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
      · intro _ seen; cases seen
      · intro d here
        obtain rfl := List.mem_singleton.mp here
        rfl

theorem genuine_closed_X4_check_has_same_model_exact_report415 :
    ∃ p, build = some p ∧ Fits p.state model ∧ ReportEvidence p.state model p.root report := by
  have yes := actual_X4_closed_record_selects_through_its_residual415
  cases ready : build with
  | none => simp [checkOpt,ready] at yes
  | some p =>
    have checked : check p report (.closedRows wire) = true := by simpa [checkOpt,ready] using yes
    have fit := actual_closed_X4_state_fits415 ready
    exact ⟨p,rfl,fit,(check_sound p report _ checked).2 model fit⟩

#eval [checkOpt, checkOpt (build [parent,child] forged),checkOpt (build [parent,child] unretained),
  checkOpt (build [parent]),checkOpt build OpenTail414.pendingReport]

#print axioms actual_X4_closed_record_selects_through_its_residual415
#print axioms X4_cannot_forge_remainder_or_skip_original_child415
#print axioms actual_closed_X4_state_fits415
#print axioms genuine_closed_X4_check_has_same_model_exact_report415
end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415.SpecX4
