import Yulang.GeneralDeclarativeI65I74RefPositionEntry441

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessSparseVariance357 (Source compile lookup)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (nominal subtype_refl)
open CommonRecursiveNominalIntervals (Endpoint)
open PresenceNormalForm (Atom)
open Checker408 (Problem Result)

def authoredRunProjection : Source 3 1 1 :=
  ⟨[⟨9,[(.row,1),(.value,0)]⟩],
    fun i => match i.val with
    | 0 => .arrow (.inl 1) .empty (.inl 2) (.var 0)
    | 1 => .arrow (.inr 0) .empty (.inr 0) .empty
    | _ => .base .unit,
    fun p => if p.val = 1 then 0 else 1⟩

def actual : Declaration := ⟨81,7,[pattern 9 6 8],[],[],[]⟩
def literal : Declaration := {actual with head := [.app 9 [.var 6,.app 20 []]]}
def reusedBinder : Declaration := {actual with head := [pattern 9 6 6]}
def rival : Declaration := {actual with id := 82,head := [.var 12]}

def surface (decls : List Declaration) : InputBundle :=
  let rows : List Row := [⟨9,some ⟨[.row,.type],9⟩,.unclassified⟩,
    ⟨20,some ⟨[],20⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,decls⟩

def registry : CommonDeclaredNominalInspection.Registry := List.replicate 9 [] ++ [layout]
def crossed : CommonDeclaredNominalInspection.Registry := List.replicate 9 [] ++ [[valueInv,rowCov]]
def roleDemand : Demand := ⟨7,[⟨0,0,0⟩],[]⟩
def authoredEndpoint : Endpoint Nat := endpoint 9 1 2
def witnessOrigin : Origin := ⟨0,[71],authoredEndpoint⟩
def exactLiteralEndpoint : Endpoint Nat :=
  .nominal 9 [rowArg 1,.inl (.point (.ordinary (.base .int)))]
def intRow : Equation := ⟨2,.primitive (.scalar .int) []⟩
def rowOne : Atom Nat := .rowLe (.var 1) (.var 1)
def valTwo : Atom Nat := .tyLe (.var 2) (.var 2)
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[rowOne,valTwo],[]⟩,[intRow]⟩

def build (decls : List Declaration := [actual])
    (modeTable : CommonDeclaredNominalInspection.Registry := registry)
    (origins : List Origin := [witnessOrigin])
    (raw : GeneralDeclarativeHead320.State := ordinary) : Option Problem := do
  let graph ← compile authoredRunProjection
  let book ← GeneralSourceMetadataBareBundle291.compile (surface decls)
  let env : Environment := ⟨3,1,1,authoredRunProjection,graph,book⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,raw,[]⟩,modeTable,origins,[]⟩
  let b6 : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,b6⟩,⟨[71],roleDemand⟩⟩

def chosen : Result := leafReport actual
def wire : Wire := ⟨0,⟨[0,1,2],[0,1,1]⟩⟩
def test (p : Option Problem := build) (r : Result := chosen)
    (w : Witness := .reference wire) : Bool := (p.map fun p => check p r w).getD false

theorem actual_run_projection_derives_ordered_modes441 :
    ((compile authoredRunProjection).bind fun c => lookup c 9) = some [rowCov,valueInv] := by
  decide +kernel

theorem actual_public_ref_role_check441 : test = true := by decide +kernel

theorem wrong_mode_order_wrong_endpoint_order_same_binder_and_rival_do_not_use_new_branch441 :
    test (build [actual] crossed) = false ∧
    test (build [actual] registry [⟨0,[71],.nominal 9 [valueArg 2,rowArg 1]⟩]) = false ∧
    test (build [reusedBinder]) = false ∧
    test (build [actual,rival]) = false ∧
    test (build [actual] registry [⟨0,[77],authoredEndpoint⟩]) = false ∧
    test build {chosen with tree := .ambiguous} = false := by decide +kernel

def literalProblem : Option Problem := build [literal] registry [⟨0,[71],exactLiteralEndpoint⟩]

theorem literal_source_problem_is_real_but_not_the_two_binder_lane441 :
    literalProblem.isSome = true ∧ test literalProblem (leafReport literal) = false := by
  decide +kernel

def rawCycle : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [intRow,⟨0,.variant 5 (.variable 0)⟩]}
def rootRawWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,0⟩,[],.same⟩
def previousRoot : Witness := .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.rawRoot rootRawWire)))))))))))))))))))))

theorem actual_unfiltered_raw_root_precedes_new_scope441 :
    test (build [actual] registry [witnessOrigin] rawCycle) = false ∧
    test (build [actual] registry [witnessOrigin] rawCycle) Check408.rawReport previousRoot = true := by
  decide +kernel

def effect : Common.Row := fun o => o = (56,[1,-2])
def model : I72.Model :=
  ⟨fun n => match n with
    | 0 => (nominal 9 [.inr effect,.inl (.base .int)],Common.rowEmpty)
    | 1 => (.bottom,effect)
    | 2 => (.base .int,Common.rowEmpty)
    | _ => (.bottom,Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some authoredEndpoint else none⟩

theorem actual_ref_with_signed_effect_fits441 {p : Problem} (h : build = some p) :
    I72.Fits p.state model := by
  unfold build at h
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at h
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [actual]) with
    | none => simp [graph,book] at h
    | some src =>
      simp only [graph,book,Option.pure_def] at h
      cases h
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a atAtom
        change a ∈ [rowOne,valTwo] at atAtom
        simp only [List.mem_cons,List.not_mem_nil,or_false] at atAtom
        rcases atAtom with rfl|rfl
        · exact Common.rowLe_refl _
        · exact subtype_refl _
      · intro _ bad; cases bad
      · intro a raw
        change a ∈ [intRow] at raw
        cases List.mem_singleton.mp raw
        exact eqv_refl _
      · intro _ bad; cases bad
      · intro o into
        change o ∈ [witnessOrigin] at into
        cases List.mem_singleton.mp into
        rfl

theorem exact_mixed_ref_dictionary_and_effect_not_value_slot441 :
    ∃ p, build = some p ∧ I72.Fits p.state model ∧
      check p chosen (.reference wire) = true ∧
      ReportEvidence p.state model p.root chosen ∧
      (model.assignment 1).2 (56,[1,-2]) ∧ ¬(model.assignment 2).2 (56,[1,-2]) := by
  have yes := actual_public_ref_role_check441
  unfold test at yes
  cases h : build with
  | none => simp [h] at yes
  | some p =>
    have ok : check p chosen (.reference wire) = true := by simpa [h] using yes
    have fit := actual_ref_with_signed_effect_fits441 h
    exact ⟨p,rfl,fit,ok,(check_sound p _ _ ok).2 _ fit,rfl,fun bad => bad⟩

#print axioms actual_run_projection_derives_ordered_modes441
#print axioms actual_public_ref_role_check441
#print axioms wrong_mode_order_wrong_endpoint_order_same_binder_and_rival_do_not_use_new_branch441
#print axioms literal_source_problem_is_real_but_not_the_two_binder_lane441
#print axioms actual_unfiltered_raw_root_precedes_new_scope441
#print axioms actual_ref_with_signed_effect_fits441
#print axioms exact_mixed_ref_dictionary_and_effect_not_value_slot441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
