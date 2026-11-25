import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419.SpecPick
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 B6MixedRhs401 MixedRhs401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty record subtype_refl)
open ClosedResidual415 (wholeExpr wholeOriginal residualExpr strRow)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def body419 : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def actual : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[body419],[]⟩
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩

def surface (table : List Declaration) (declared : Bool) : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,
    ⟨1,if declared then [⟨7,1,[(3,none)]⟩,⟨9,0,[]⟩] else [⟨9,0,[]⟩]⟩,table⟩

def rootRow : Equation := ⟨0,wholeExpr 20 1 21 2⟩
def xRow : Equation := OpenTail414.intRow 1
def yRow : Equation := strRow 2
def tailRow : Equation := ⟨3,residualExpr 21 2⟩
def splitRow : Equation := OpenTail414.openRow 0 20 1 3
def outRow : Equation := ⟨4,.variable 1⟩
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,xRow,yRow,tailRow,splitRow,outRow]⟩

def build (table : List Declaration := [unrelated,actual])
    (raw : GeneralDeclarativeHead320.State := ordinary)
    (declared : Bool := true) (typed : Bool := true) (declIndex : Nat := 1)
    (request : List Nat := [61]) (target : Nat := 4) : Option Problem := do
  let program ← compile bodies
  let bundle ← GeneralSourceMetadataBareBundle291.compile (surface table declared)
  let env : Environment := ⟨0,0,0,bodies,program,bundle⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,raw,[]⟩,[],[⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun q ordinal i b =>
    if typed && q.occurrence == [61] && ordinal == declIndex && i.val == 0 then
      if h : b = .explicit body419 then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 state false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit body419)))))
      else none
    else none⟩
  pure ⟨⟨state,atlas⟩,⟨request,⟨7,[⟨0,0,0⟩],[⟨3,target⟩]⟩⟩⟩

def wire : PickWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,1],[0,1,1,2]⟩⟩
def expected : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[⟨[61],1,0,⟨3,4⟩,.explicit body419,.node 0 [8,1,1,1] []⟩]⟩

def checkOpt (p : Option Problem := build) (r : Result := expected)
    (w : Witness := .explicitPick wire) : Bool :=
  (p.map fun p => check p r w).getD false

theorem actual_Pick_from_spec_has_nonempty_original_input_and_output419 : checkOpt = true := by
  decide +kernel

def actualResidualTy : Ty := record 21 (.base .str) .emptyRecord
def actualInputTy : Ty := record 20 (.base .int) actualResidualTy

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then actualInputTy else if n = 2 then .base .str
                  else if n = 3 then actualResidualTy else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem original_Pick_nonempty_source_has_fitting_model419 {p : Problem} (ready : build = some p) :
    Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [unrelated,actual] true) with
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

theorem genuine_Pick_has_exact_same_model_dictionary_output419 :
    ∃ p, build = some p ∧ Fits p.state model ∧
      ReportEvidence p.state model p.root expected ∧
      DictionaryEvidence p.state model p.root (.node 57 []) := by
  have yes := actual_Pick_from_spec_has_nonempty_original_input_and_output419
  cases got : build with
  | none => simp [checkOpt,got] at yes
  | some p =>
    have checked : check p expected (.explicitPick wire) = true := by simpa [checkOpt,got] using yes
    have fit := original_Pick_nonempty_source_has_fitting_model419 got
    have report := check_sound p expected (.explicitPick wire) checked
    exact ⟨p,rfl,fit,report.2 model fit,
      dictionary_sound_R11 _ _ _ (exact_report_is_R11_classification419 report.1) model fit⟩

def wrongBody : Declaration := {actual with associated := [{body419 with rhs := .var 13}]}
def noRetainedRow : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,xRow,yRow,tailRow,splitRow]}
def unwrittenEquivalent : GeneralDeclarativeHead320.State :=
  {ordinary with equations := noRetainedRow.equations ++ [OpenTail414.intRow 4]}
def increased : GeneralDeclarativeHead320.State :=
  {ordinary with equations := noRetainedRow.equations ++ [⟨5,.variable 1⟩]}
def moved : Result := {expected with writes := expected.writes.map fun w =>
  {w with target := ⟨3,5⟩}}
def movedWire : PickWire := {wire with rootEscape := ⟨[0,1,2,3,1,1],[0,1,1,2]⟩}
def bothOutputs (p : Problem) : Problem := {p with root :=
  {p.root with demand := {p.root.demand with outputs := [⟨3,4⟩,⟨3,5⟩]}}}

theorem check_does_not_invent_typed_child_scope_or_fixed_row419 :
    checkOpt (build [unrelated,actual] ordinary false) = false ∧
    checkOpt (build [unrelated,actual] ordinary true false) = false ∧
    checkOpt (build (request := [62])) = false ∧
    checkOpt (build (declIndex := 0)) = false ∧
    checkOpt (build (target := 5)) = false ∧
    checkOpt (build [unrelated,wrongBody]) = false ∧
    checkOpt (build [unrelated,actual] noRetainedRow) = false ∧
    checkOpt (build [unrelated,actual] unwrittenEquivalent) = false ∧
    checkOpt (build [unrelated,actual] increased (target := 5)) expected (.explicitPick movedWire) = false ∧
    checkOpt (build [unrelated,actual] increased (target := 5)) moved (.explicitPick movedWire) = true ∧
    checkOpt (build.map bothOutputs) = false := by decide +kernel

def mutate (f : Check408.Write → Check408.Write) : Result :=
  {expected with writes := expected.writes.map f}

theorem emitted_literal_ledger_checks_every_coordinate419 :
    checkOpt build (mutate fun w => {w with occurrence := [62]}) = false ∧
    checkOpt build (mutate fun w => {w with declarationOrdinal := 0}) = false ∧
    checkOpt build (mutate fun w => {w with outputOrdinal := 1}) = false ∧
    checkOpt build (mutate fun w => {w with target := ⟨4,4⟩}) = false ∧
    checkOpt build (mutate fun w => {w with body := .explicit {body419 with id := 93}}) = false ∧
    checkOpt build (mutate fun w => {w with typedRhs := .node 0 [8,1,3,1] []}) = false ∧
    checkOpt build {expected with writes := expected.writes ++ expected.writes} = false ∧
    checkOpt build {expected with writes := []} = false ∧
    checkOpt build expected (.explicitPick {wire with outputRow := 4}) = false ∧
    checkOpt build expected (.explicitPick {wire with declaration := 0}) = false :=
  by decide +kernel

def rootCycle : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [⟨1,.variable 0⟩]}
def offRoute : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [⟨6,.variant 90 (.variable 6)⟩]}
def offRouteWire : PickWire :=
  {wire with rootEscape := ⟨[0,1,2,3,1,3,3],[0,1,1,2]⟩}
def rawWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨0,.same,1⟩,[],.forward 6⟩
def legacyRoot : Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.rawRoot rawWire)))))))))))

theorem raw_root_beats_even_missing_B6_but_offroute_is_not_a_visit419 :
    checkOpt (build (raw := rootCycle)) = false ∧
    checkOpt (build (raw := rootCycle) (typed := false))
      Check408.rawReport legacyRoot = true ∧
    checkOpt (build (raw := offRoute)) expected (.explicitPick offRouteWire) = true := by
  decide +kernel

#eval checkOpt
#print axioms actual_Pick_from_spec_has_nonempty_original_input_and_output419
#print axioms original_Pick_nonempty_source_has_fitting_model419
#print axioms genuine_Pick_has_exact_same_model_dictionary_output419
#print axioms check_does_not_invent_typed_child_scope_or_fixed_row419
#print axioms emitted_literal_ledger_checks_every_coordinate419
#print axioms raw_root_beats_even_missing_B6_but_offroute_is_not_a_visit419
end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419.SpecPick
