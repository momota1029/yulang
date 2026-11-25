import Yulang.GeneralDeclarativeI65I74RoleDefaultCoherence420

namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420.NativeDefault
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 B6MixedRhs401 MixedRhs401)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty record subtype_refl)
open ExplicitPick419 (pickSyntax inputView exactlyOneOutput replayOutput)
open ClosedResidual415 (wholeExpr wholeOriginal residualExpr strRow readRows415)

def bodySource : Source 3 0 0 :=
  ⟨[⟨90,[]⟩],
    fun i => if i.val = 0 then .union (.variant 3 (.inl 1)) (.variant 4 (.inl 2))
      else if i.val = 1 then .nominal 90 [] else .base .unit,
    fun i => i.elim0⟩

def defaultBody : Body := .default 7 3 (.app 90 [])
def actual : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[],[]⟩
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩

def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨1,[⟨7,1,[(3,some (.app 90 []))]⟩,⟨9,0,[]⟩]⟩,
    [unrelated,actual]⟩

def ordinary : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,wholeExpr 20 1 21 2⟩,OpenTail414.intRow 1,strRow 2,
    ⟨3,residualExpr 21 2⟩,OpenTail414.openRow 0 20 1 3,⟨4,.nominal 90 []⟩]⟩

def build (typed : Bool := true) : Option Problem := do
  let program ← compile bodySource
  let bundle ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨3,0,0,bodySource,program,bundle⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 91 [],[⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩
  let u ← readUse env 90 0
  if md : names u.mode 0 = some [] then
    let atlas : B6OccurrenceAtlas401 state := ⟨fun q ordinal i b =>
      if typed && q.occurrence == [79] && ordinal == 1 && i.val == 0 then
        if h : b = defaultBody then
          some (h.symm ▸ (.declaredApp 90 u md (by rfl) .nil :
            B6MixedRhs401 state false
              (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern defaultBody))))
        else none
      else none⟩
    pure ⟨⟨state,atlas⟩,⟨[79],⟨7,[⟨0,0,0⟩],[⟨3,4⟩]⟩⟩⟩
  else none

def wire : DefaultWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,3],[0,1,1,2]⟩⟩
def expected : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[⟨[79],1,0,⟨3,4⟩,defaultBody,.node 4 [90] []⟩]⟩
def probe (p : Option Problem := build) (r : Result := expected)
    (w : Witness := .roleDefault wire) : Bool :=
  (p.map fun q => check q r w).getD false

theorem default_literal_native_source_body_is_recursive420 :
    bodySource.bodies 1 = .nominal 90 [] := rfl

theorem actual_declared_nominal_default_is_accepted420 :
    probe = true := by decide +kernel

theorem default_modes_are_read_natively_not_faked_as_invariant420 :
    (build.map fun p =>
      GeneralDeclarativeWitnessProblem349.covered p.state.core.current.environment.source).getD true = false ∧
    (build.map fun p => checkHeader p.state.core.current.environment).getD false = true := by
  decide +kernel

def read_actual_declared_mode (p : Problem) : Bool :=
  match readUse p.state.core.current.environment 90 0 with
  | some u => match u.mode with | .declared [] => true | _ => false
  | none => false

theorem actual_closed_default_uses_authored_declared_mode420 :
    (build.map read_actual_declared_mode).getD false = true := by decide +kernel

theorem declared_default_does_not_trust_wrong_occurrence_or_rhs420 :
    probe (build false) = false ∧
    probe build expected (.roleDefault {wire with declaration := 0}) = false ∧
    probe build {expected with writes := expected.writes.map (fun out =>
      {out with typedRhs := .node 4 [91] []})} = false := by decide +kernel

def actualResidualTy : Ty := record 21 (.base .str) .emptyRecord
def actualInputTy : Ty := record 20 (.base .int) actualResidualTy

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then actualInputTy else if n = 2 then .base .str else
        if n = 3 then actualResidualTy else if n = 4 then CommonNominalFullCarrier.nominal 90 [] else
          .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem actual_declared_nominal_default_has_fitting_model420 {p : Problem}
    (ready : build = some p) : Fits p.state model := by
  unfold build at ready
  cases cp : compile bodySource with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile surface with
    | none => simp [cp,cm] at ready
    | some bundle =>
      let e : Environment := ⟨3,0,0,bodySource,program,bundle⟩
      cases has : readUse e 90 0 with
      | none =>
        have bad : readUse ⟨3,0,0,bodySource,program,bundle⟩ 90 0 = none := has
        simp [cp,cm,bad] at ready
      | some use =>
        have good : readUse ⟨3,0,0,bodySource,program,bundle⟩ 90 0 = some use := has
        simp only [cp,cm,good,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at ready
        split at ready
        · cases Option.some.inj ready
          refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
          · intro _ seen; cases seen
          · intro _ seen; cases seen
          · intro x found
            change x ∈ [⟨0,wholeExpr 20 1 21 2⟩,OpenTail414.intRow 1,strRow 2,
              ⟨3,residualExpr 21 2⟩,OpenTail414.openRow 0 20 1 3,⟨4,.nominal 90 []⟩] at found
            simp only [List.mem_cons,List.not_mem_nil,or_false] at found
            rcases found with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
          · intro _ seen; cases seen
          · intro x found
            obtain rfl := List.mem_singleton.mp found
            rfl
        · contradiction

theorem genuine_native_role_default_has_same_model_dictionary420 :
    ∃ p, build = some p ∧ Fits p.state model ∧
      ReportEvidence p.state model p.root expected ∧
      DictionaryEvidence p.state model p.root (.node 57 []) := by
  have yes := actual_declared_nominal_default_is_accepted420
  cases got : build with
  | none => simp [probe,got] at yes
  | some p =>
    have checked : check p expected (.roleDefault wire) = true := by simpa [probe,got] using yes
    have fit := actual_declared_nominal_default_has_fitting_model420 got
    have report := check_sound p expected (.roleDefault wire) checked
    exact ⟨p,rfl,fit,report.2 model fit,
      dictionary_sound_R12 _ _ _ (exact_report_is_R12_classification420 report.1) model fit⟩

#print axioms default_literal_native_source_body_is_recursive420
#print axioms actual_declared_nominal_default_is_accepted420
#print axioms default_modes_are_read_natively_not_faked_as_invariant420
#print axioms actual_closed_default_uses_authored_declared_mode420
#print axioms declared_default_does_not_trust_wrong_occurrence_or_rhs420
#print axioms actual_declared_nominal_default_has_fitting_model420
#print axioms genuine_native_role_default_has_same_model_dictionary420
end Yulang.GeneralDeclarativeI65.I72.RoleDefault420.NativeDefault
