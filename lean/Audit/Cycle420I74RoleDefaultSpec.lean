import Yulang.GeneralDeclarativeI65I74RoleDefaultLocator420

namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420.SpecDefault
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 B6MixedRhs401 MixedRhs401)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty record subtype_refl)
open ExplicitPick419 (pickSyntax)
open ClosedResidual415 (wholeExpr wholeOriginal residualExpr strRow)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def defaultBody : Body := .default 7 3 (.var 0)
def explicitBody : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def otherBody : GeneralDeclarations.Equation := ⟨93,4,.var 13⟩
def actual : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[],[]⟩
def override : Declaration := {actual with associated := [explicitBody]}
def otherExplicit : Declaration := {actual with associated := [otherBody]}
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩

def surface (table : List Declaration) (ownerDefault : Option Roles.Term) : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨1,[⟨7,1,[(3,ownerDefault),(4,some (.var 0))]⟩,⟨9,0,[]⟩]⟩,table⟩

def rootRow : Equation := ⟨0,wholeExpr 20 1 21 2⟩
def xRow : Equation := OpenTail414.intRow 1
def yRow : Equation := strRow 2
def tailRow : Equation := ⟨3,residualExpr 21 2⟩
def splitRow : Equation := OpenTail414.openRow 0 20 1 3
def outRow : Equation := ⟨4,.variable 0⟩
def explicitRow : Equation := ⟨4,.variable 1⟩
def ordinary : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRow,xRow,yRow,tailRow,splitRow,outRow]⟩
def explicitOrdinary : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,xRow,yRow,tailRow,splitRow,explicitRow]}

def build (table : List Declaration := [unrelated,actual])
    (raw : GeneralDeclarativeHead320.State := ordinary)
    (ownerDefault : Option Roles.Term := some (.var 0)) (typed : Bool := true)
    (declIndex : Nat := 1) (request : List Nat := [61]) (target : Nat := 4) : Option Problem := do
  let program ← compile bodies
  let bundle ← GeneralSourceMetadataBareBundle291.compile (surface table ownerDefault)
  let env : Environment := ⟨0,0,0,bodies,program,bundle⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,raw,[]⟩,[],[⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun q ordinal i b =>
    if typed && q.occurrence == [61] && ordinal == declIndex && i.val == 0 then
      if h : b = defaultBody then
        some (h.symm ▸ (MixedRhs401.binder 0 () : B6MixedRhs401 state false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern defaultBody))))
      else if h : b = .explicit explicitBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 state false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit explicitBody)))))
      else none
    else none⟩
  pure ⟨⟨state,atlas⟩,⟨request,⟨7,[⟨0,0,0⟩],[⟨3,target⟩]⟩⟩⟩

def wire : DefaultWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,0],[0,1,1,2]⟩⟩
def overrideWire : ExplicitPick419.PickWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,1],[0,1,1,2]⟩⟩
def expected : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[⟨[61],1,0,⟨3,4⟩,defaultBody,.node 0 [0,0,0,0] []⟩]⟩
def overrideExpected : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[⟨[61],1,0,⟨3,4⟩,.explicit explicitBody,.node 0 [8,1,1,1] []⟩]⟩

def checkOpt (p : Option Problem := build) (r : Result := expected)
    (w : Witness := .roleDefault wire) : Bool :=
  (p.map fun p => check p r w).getD false

theorem actual_owner_default_selects_and_writes_the_whole_argument420 :
    checkOpt = true := by decide +kernel

theorem only_explicit_for_the_same_name_suppresses_role_default420 :
    checkOpt (build [unrelated,override]) = false ∧
    checkOpt (build [unrelated,override] explicitOrdinary) overrideExpected
      (.previous (.explicitPick overrideWire)) = true ∧
    checkOpt (build [unrelated,override] explicitOrdinary) expected
      (.previous (.explicitPick overrideWire)) = false ∧
    checkOpt (build [unrelated,otherExplicit]) = true := by decide +kernel

theorem role_default_cannot_be_guessed_or_retagged420 :
    checkOpt (build (ownerDefault := none)) = false ∧
    checkOpt (build (ownerDefault := some (.var 1))) = false ∧
    checkOpt (build (typed := false)) = false ∧
    checkOpt (build (declIndex := 0)) = false ∧
    checkOpt (build (request := [62])) = false ∧
    checkOpt build overrideExpected = false ∧
    checkOpt build expected (.roleDefault {wire with outputRow := 4}) = false ∧
    checkOpt (build (target := 5)) = false ∧
    checkOpt (build (raw := explicitOrdinary)) = false := by decide +kernel

def actualResidualTy : Ty := record 21 (.base .str) .emptyRecord
def actualInputTy : Ty := record 20 (.base .int) actualResidualTy

def model : I72.Model :=
  ⟨fun n => ((if n = 0 ∨ n = 4 then actualInputTy else if n = 2 then .base .str
                  else if n = 3 then actualResidualTy else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem default_projection_fixture_has_fitting_model420 {p : Problem} (ready : build = some p) :
    Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [unrelated,actual] (some (.var 0))) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ seen; cases seen
      · intro _ seen; cases seen
      · intro x found
        change x ∈ [rootRow,xRow,yRow,tailRow,splitRow,outRow] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
      · intro _ seen; cases seen
      · intro d here
        obtain rfl := List.mem_singleton.mp here
        rfl

theorem genuine_role_default_has_same_model_dictionary420 :
    ∃ p, build = some p ∧ Fits p.state model ∧
      ReportEvidence p.state model p.root expected ∧
      DictionaryEvidence p.state model p.root (.node 57 []) := by
  have yes := actual_owner_default_selects_and_writes_the_whole_argument420
  cases got : build with
  | none => simp [checkOpt,got] at yes
  | some p =>
    have checked : check p expected (.roleDefault wire) = true := by simpa [checkOpt,got] using yes
    have fit := default_projection_fixture_has_fitting_model420 got
    have report := check_sound p expected (.roleDefault wire) checked
    exact ⟨p,rfl,fit,report.2 model fit,
      dictionary_sound_R12 _ _ _ (exact_report_is_R12_classification420 report.1) model fit⟩

#print axioms actual_owner_default_selects_and_writes_the_whole_argument420
#print axioms only_explicit_for_the_same_name_suppresses_role_default420
#print axioms role_default_cannot_be_guessed_or_retagged420
#print axioms default_projection_fixture_has_fitting_model420
#print axioms genuine_role_default_has_same_model_dictionary420
end Yulang.GeneralDeclarativeI65.I72.RoleDefault420.SpecDefault
