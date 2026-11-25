import Yulang.GeneralDeclarativeI65I74OpenTailModels414

namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414.RootAndModelX4
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
def original : Declaration := ⟨57,7,[openHead 27 9 8],[tailRequirement 7 8 66],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[openRow 0 27 1 2,intRow 1]⟩

def build (rows : List Declaration := [original]) (ordinary : GeneralDeclarativeHead320.State := raw)
    (origins : List GeneralDeclarativeI65.Origin := [⟨0,[22],openTerm 27 1 2⟩]) :
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

theorem X4_pending_checked_on_second_independent_raw_input414 :
    checkOpt build = true := by decide +kernel

theorem X4_concrete_one_state_two_models414 :
    ∃ p, build = some p ∧ ∃ a : OpenInput p.state p.root, ∃ m n : I72.Model,
      Fits p.state m ∧ Fits p.state n ∧ (m.assignment a.tail).1 ≠ (n.assignment a.tail).1 ∧
      ReportEvidence p.state m p.root pendingReport ∧ ReportEvidence p.state n p.root pendingReport := by
  have yes := X4_pending_checked_on_second_independent_raw_input414
  cases ready : build with
  | none => simp [checkOpt,ready] at yes
  | some p =>
    have checked : check p pendingReport (.openTail wire) = true := by
      simp [checkOpt,ready] at yes
      exact yes
    have one : p.state.core.origins = [⟨0,[22],openTerm 27 1 2⟩] := by
      unfold build at ready
      expose_names
      cases cp : compile bodies with
      | none => simp [cp] at ready
      | some program =>
        cases bundle : GeneralSourceMetadataBareBundle291.compile (surface [original]) with
        | none => simp [cp,bundle] at ready
        | some source => simp [cp,bundle] at ready; subst p; rfl
    have exactOrigin : ∀ v : OpenVerified p, replayOpen414 p wire = some v →
        p.state.core.origins = [v.pending.input.origin] := by
      intro v _
      have includes := v.pending.input.original
      rw [one] at includes
      rw [one,List.mem_singleton.mp includes]
    obtain ⟨a,m,n,mFit,nFit,_,_,diff,mEvidence,nEvidence⟩ :=
      one_checked_state_has_two_tail_models414 p wire checked exactOrigin 42
    exact ⟨p,rfl,a,m,n,mFit,nFit,diff,mEvidence,nEvidence⟩

def nativeRootCycle : Equation := ⟨0,.record 27 (.variable 1)
    (.record 42 (.variable 0) (.primitive .emptyRecord []))⟩
def rootCycleRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [nativeRootCycle]}
def rawRoot : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨2,.same,0⟩,[],.same⟩

theorem X4_unfiltered_actual_root_K2_remains_first414 :
    checkOpt (build [original] rootCycleRaw) = false ∧
    checkOpt (build [original] rootCycleRaw) Check408.rawReport
      (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawRoot))))))) = true := by
  decide +kernel

#eval [checkOpt build,checkOpt (build [original] rootCycleRaw),
  checkOpt (build [original] rootCycleRaw) Check408.rawReport
    (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawRoot)))))))]
#print axioms X4_pending_checked_on_second_independent_raw_input414
#print axioms X4_concrete_one_state_two_models414
#print axioms X4_unfiltered_actual_root_K2_remains_first414

end Yulang.GeneralDeclarativeI65.I72.OpenTail414.RootAndModelX4
