import Yulang.GeneralDeclarativeI65I74PlainMergedConservative416

namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416.ControlsX6
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 SourceHead)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty variant subtype_refl)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def actual : Declaration := ⟨57,7,[sourceX6 20 8 13],[],[],[]⟩
def ground : Declaration := ⟨58,7,[.variant 20 (.app 9 [])],[],[],[]⟩

def surface (ds : List Declaration) (declared : Bool) : InputBundle :=
  let tags : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,tags⟩,⟨.absent,tags⟩,⟨1,if declared then [⟨7,1,[]⟩,⟨9,1,[]⟩] else []⟩,ds⟩

def rootRow : Equation := variantRow416 0 20 1
def intRow : Equation := OpenTail414.intRow 1
def joinRow : Equation := idempotentRow 0
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,intRow,joinRow]⟩

def build (ds : List Declaration := [actual])
    (raw : GeneralDeclarativeHead320.State := ordinary) (declared : Bool := true) :
    Option Problem := do
  let program ← compile bodies
  let src ← GeneralSourceMetadataBareBundle291.compile (surface ds declared)
  let e : Environment := ⟨0,0,0,bodies,program,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨e,raw,[]⟩,[],[⟨0,[44],originX6 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : PlainWire := ⟨0,0,1,2,0,⟨[0,1],[0,1]⟩⟩
def report : Result := Check408.nullaryReport actual
def checkOpt (p : Option Problem := build) (r : Result := report)
    (w : Witness := .plainMerged wire) : Bool :=
  (p.map fun data => check data r w).getD false

def locations (p : Option Problem) (w : PlainWire := wire) : Option PlainLocation := do
  let p ← p
  locate p w

def flipped : Declaration := {actual with head := [sourceX6 20 13 8]}
def independentRole : Declaration := {ground with role := 9}
def remapped : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [joinRow,intRow,rootRow]}
def remappedWire : PlainWire := {wire with variantRow := 2,joinRow := 0,declaration := 1}

theorem actual_source_order_is_kept_while_capture_is_the_same416 :
    checkOpt (build [independentRole,flipped] remapped) (Check408.nullaryReport flipped)
      (.plainMerged remappedWire) = true ∧
    locations build = some ⟨[61],57,0,0,20,1,8,13⟩ ∧
    locations (build [independentRole,flipped] remapped) remappedWire =
      some ⟨[61],57,1,0,20,1,13,8⟩ := by decide +kernel

def twoRoots : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 0 20 2,OpenTail414.intRow 2]}

theorem a_second_same_typed_slot_is_not_the_authoritative_source416 :
    checkOpt (build [actual] twoRoots) = false ∧
    checkOpt (build [actual] twoRoots) report
      (.plainMerged {wire with variantRow := 3,intRow := 4}) = false := by decide +kernel

def rawRootCycle : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [RecordK2412.recordRow412 0 99 0]}
def rawWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨3,.same,0⟩,[],.same⟩
def priorRaw : Witness := .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawWire))))))))

theorem unfiltered_actual_K2_still_has_priority416 :
    checkOpt (build [actual] rawRootCycle) = false ∧
    checkOpt (build [actual] rawRootCycle) Check408.rawReport priorRaw = true := by decide +kernel

def noJoin : GeneralDeclarativeHead320.State := {ordinary with equations := [rootRow,intRow]}
def knownInt : Ty := .base .int
def noJoinModel : I72.Model :=
  ⟨fun n => ((if n = 0 then variant 20 knownInt else knownInt),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (originX6 20 1) else none⟩

theorem no_join_fixture_still_fits416 {p : Problem} (ready : build [actual] noJoin = some p) :
    Fits p.state noJoinModel ∧ p.root.demand.arguments = [⟨0,0,0⟩] ∧
      ¬ HasOriginalJoin p.state.core.current.ordinary 0 := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [actual] true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      refine ⟨?_,rfl,?_⟩
      · refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
        · intro _ bad; cases bad
        · intro _ bad; cases bad
        · intro x found
          change x ∈ [rootRow,intRow] at found
          simp only [List.mem_cons,List.not_mem_nil,or_false] at found
          rcases found with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
        · intro _ bad; cases bad
        · intro x seen
          obtain rfl := List.mem_singleton.mp seen
          rfl
      · rintro ⟨l,r,bad⟩
        simp [noJoin,rootRow,intRow,variantRow416,OpenTail414.intRow] at bad

theorem real_fitting_X6_without_join_lacks_the_fixed_source_read416 :
    ∃ p, build [actual] noJoin = some p ∧ Fits p.state noJoinModel ∧
      ¬ Nonempty (SourceHead p.state.core p.root actual) ∧ check p report (.plainMerged wire) = false := by
  have executable : checkOpt (build [actual] noJoin) = false := by decide +kernel
  cases built : build [actual] noJoin with
  | none =>
    have bad : (build [actual] noJoin).isSome = true := by decide +kernel
    simp [built] at bad
  | some p =>
    obtain ⟨fit,arg,noRead⟩ := no_join_fixture_still_fits416 built
    refine ⟨p,rfl,fit,?_,by simpa [checkOpt,built] using executable⟩
    rintro ⟨actualRead⟩
    exact noRead (exact_plain_source_head_needs_a_real_join416 (show 8 ≠ 13 by decide) arg rfl actualRead)

theorem the_witness_only_extension_is_exactly_the_existing_fixture416 :
    withRedundantRead noJoin 0 = ordinary ∧
    (∀ m, GeneralDeclarativeHead320.Models ordinary m ↔ GeneralDeclarativeHead320.Models noJoin m) ∧
    (∀ site, List410.checkExactEscape ordinary site wire.rootEscape =
        List410.checkExactEscape noJoin site wire.rootEscape) :=
  ⟨rfl,fun m => a_redundant_read_never_changes_model_solutions416 noJoin 0 m,
    fun site => a_redundant_read_preserves_raw_guard416 noJoin 0 site wire.rootEscape⟩

#eval [checkOpt (build [independentRole,flipped] remapped) (Check408.nullaryReport flipped) (.plainMerged remappedWire),
  checkOpt (build [actual] twoRoots),checkOpt (build [actual] rawRootCycle),
  checkOpt (build [actual] rawRootCycle) Check408.rawReport priorRaw]
#print axioms actual_source_order_is_kept_while_capture_is_the_same416
#print axioms a_second_same_typed_slot_is_not_the_authoritative_source416
#print axioms unfiltered_actual_K2_still_has_priority416
#print axioms no_join_fixture_still_fits416
#print axioms real_fitting_X6_without_join_lacks_the_fixed_source_read416
#print axioms the_witness_only_extension_is_exactly_the_existing_fixture416
end Yulang.GeneralDeclarativeI65.I72.PlainMerged416.ControlsX6
