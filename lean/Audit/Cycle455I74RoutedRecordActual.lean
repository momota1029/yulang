import Yulang.GeneralDeclarativeI65I74RoutedRecordEntry455

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
namespace Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.Spec
open Yulang.GeneralDeclarativeI65
open RetainedFull445 RecordTraversal455
open RecordTrail455 (Form chain FieldReport tokenOps)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent record)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open List410 (ExactEscapeWire)
open RecordK2412 (FieldCycleWire)
open GeneralDeclarativeWitnessDeclaredState357 (point)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def f : Form := ⟨9,3,[10,20,30,40],[10]⟩
def badShallow : Form := ⟨9,3,[10,20,30],[10]⟩
def branched (f : Form) : Pattern :=
  .record 10 (chain f.empty f.writtenHead.tail (.var f.binder))
    (.record 90 (.var 99) (.app f.empty []))

def originalImpl (form : Form) : Declaration :=
  ⟨218,19,[branched form],[⟨6,19,form.condition,[]⟩],[],[]⟩
def surface (form : Form) : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[originalImpl form]⟩

def empty : Expr := .primitive .emptyRecord []
def outer : Expr := .record 10 (.variable 1) (.record 90 (.variable 9) empty)
def oneRow (i field child : Nat) : Equation := ⟨i,.record field (.variable child) empty⟩

def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,outer⟩,⟨1,.variable 11⟩,oneRow 11 20 2,oneRow 2 30 3,
    oneRow 3 40 3,oneRow 9 90 9]⟩
def outside : TyTerm Nat :=
  .record 10 (.var 1) (.record 90 (.var 9) .emptyRecord)
def middle : TyTerm Nat := .record 20 (.var 2) .emptyRecord
def lastOpened : TyTerm Nat := .record 30 (.var 3) .emptyRecord
def origins : List Origin :=
  [⟨0,[401],.ordinary outside⟩,⟨11,[402],.ordinary middle⟩,⟨2,[403],.ordinary lastOpened⟩]
def rawMiddleOnly : List Origin :=
  [⟨0,[401],.ordinary outside⟩,⟨1,[402],.ordinary middle⟩,⟨2,[403],.ordinary lastOpened⟩]

def actualRoutes : List GeneralDeclarativeI65.Alias := [⟨1,11,[402]⟩]

def build (form : Form) (s : GeneralDeclarativeHead320.State) (srcs : List Origin)
    (routes : List GeneralDeclarativeI65.Alias := actualRoutes) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile (surface form)
  let env : Environment := ⟨0,0,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,[],srcs,routes⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)

def p : FullProblem := (build f raw origins).get (by decide +kernel)
def missingRoute : FullProblem := (build f raw origins []).get (by decide +kernel)
def wrongIssuer : FullProblem := (build f raw origins [⟨1,11,[777]⟩]).get (by decide +kernel)
def missingOwner : FullProblem := (build f raw rawMiddleOnly).get (by decide +kernel)
def capturedAt3 : FullProblem := (build badShallow raw origins).get (by decide +kernel)
def earlierRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [oneRow 1 88 1]}
def earlier : FullProblem := (build f earlierRaw origins []).get (by decide +kernel)
def parentRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨1,.variable 0⟩]}
def parentCycle : FullProblem := (build f parentRaw origins).get (by decide +kernel)

def esc0 : ExactEscapeWire := ⟨List.range 12,[0,1,1,1,2,2,2,2,2,1,2,1]⟩
def esc1 : ExactEscapeWire := ⟨List.range 12,[2,0,1,1,2,2,2,2,2,2,2,0]⟩
def esc2 : ExactEscapeWire := ⟨List.range 12,[2,2,0,1,2,2,2,2,2,2,2,2]⟩

def path : TrailWire tokenOps :=
  .down ⟨0,.same,0,0,(0 : Nat)⟩ esc0
    (.down ⟨2,.forward 1,0,0,(1 : Nat)⟩ esc1
      (.down ⟨3,.same,0,0,(2 : Nat)⟩ esc2 .stop))
def wrongAlias : TrailWire tokenOps :=
  .down ⟨0,.same,0,0,(0 : Nat)⟩ esc0
    (.down ⟨2,.same,0,0,(1 : Nat)⟩ esc1
      (.down ⟨3,.same,0,0,(2 : Nat)⟩ esc2 .stop))
def unvisited : TrailWire tokenOps := .down ⟨0,.same,1,1,(0 : Nat)⟩ esc0 .stop
def finalCycle : FieldCycleWire := ⟨⟨4,.same,3⟩,[],.same⟩
def outsideCycle : FieldCycleWire := ⟨⟨5,.same,9⟩,[],.same⟩
def wire : FieldWire := ⟨9,⟨path,finalCycle⟩⟩
def good : FieldReport := ⟨[71,2],218,[(10,1),(20,2),(30,3)],3⟩
def expectedEarly : FieldReport := ⟨[71,2],218,[(10,1)],1⟩
def earlierWire : FieldWire := ⟨9,⟨.down ⟨0,.same,0,0,(0 : Nat)⟩ esc0 .stop,⟨⟨6,.same,1⟩,[],.same⟩⟩⟩
def check (a : FullProblem) (r : FieldReport) (w : FieldWire) : Bool :=
  check_full455 a (.fieldK2 r) (.fieldK2 w)

/-- info: [true, false, false, false, false, false, false, false, false, false, true, false, false] -/
#guard_msgs in
#eval [check p good wire,check p {good with occurrence := [71]} wire,
  check p {good with declaration := 217} wire,
  check p ⟨[71,2],218,[(90,9)],9⟩ ⟨9,⟨unvisited,outsideCycle⟩⟩,
  check p good ⟨9,⟨wrongAlias,finalCycle⟩⟩,
  check missingOwner good wire,check missingRoute good wire,check wrongIssuer good wire,
  check capturedAt3 good ⟨9,⟨path,finalCycle⟩⟩,
  check earlier good wire,check earlier expectedEarly earlierWire,
  check parentCycle good wire,check p {good with terminalSite := 9} wire]

def recState (field : Nat) : CommonNominalSyntax.State Common.Row :=
  .block [.record field (.inl 0) .emptyRecord] 0
def mu (field : Nat) : Ty := .record field (recState field) .emptyRecord
theorem unfold_mu455 (f : Nat) :
    Equivalent (mu f) (record f (mu f) .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k (mu f) =
      CommonNominalFullCarrier.observeTy k (record f (mu f) .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [←each k]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each k]
    exact CommonNominalFullDemand.producerLe_refl _

def tyAt2 : Ty := record 30 (mu 40) .emptyRecord
def tyAt1 : Ty := record 20 tyAt2 .emptyRecord
def tyAt0 : Ty := record 10 tyAt1 (record 90 (mu 90) .emptyRecord)
def assign (x : Nat) : Ty :=
  if x = 0 then tyAt0 else if x = 2 then tyAt2 else if x = 3 then mu 40 else
    if x = 9 then mu 90 else tyAt1

def model : I72.Model :=
  ⟨fun n => (assign n,Common.rowEmpty),fun _ => none,fun n =>
    if n = 0 then some (.ordinary outside) else if n = 11 then some (.ordinary middle) else
      if n = 2 then some (.ordinary lastOpened) else none⟩

theorem routed_branch_actual_program_has_full_fit455 : FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro row seen
    change row ∈ [⟨0,outer⟩,⟨1,.variable 11⟩,oneRow 11 20 2,oneRow 2 30 3,
      oneRow 3 40 3,oneRow 9 90 9] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact unfold_mu455 40
    · exact unfold_mu455 90
  · intro _ bad; cases bad
  · intro src real
    change src ∈ origins at real
    simp only [origins,List.mem_cons,List.not_mem_nil,or_false] at real
    rcases real with rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

theorem routed_branch_depth_three_gives_same_model455 :
    FieldEvidence p.old model good := by
  have executable : check p good wire = true := by decide +kernel
  exact (check_full_sound455 p (.fieldK2 good) (.fieldK2 wire) executable).2 model
    routed_branch_actual_program_has_full_fit455

theorem routed_cyclic_variable_sibling_is_never_an_inspection455 :
    GeneralDeclarativeK2Alias321.AliasCycle raw (GeneralDeclarativeGraphRows321.observed raw) 9 ∧
      check p ⟨[71,2],218,[(90,9)],9⟩ ⟨9,⟨unvisited,outsideCycle⟩⟩ = false := by
  exact ⟨RecordK2412.cycle_at_sound412 (w := outsideCycle) (by decide +kernel),by decide +kernel⟩

theorem same_raw_alias_and_native_origin_do_not_replace_the_authored_route455 :
    GeneralDeclarativeLowerKnown321.Alias raw 1 11 ∧
      RecordTrail455.SourceOpen missingRoute.state.base.core (oneRow 11 20 2) ∧
      check p good wire = true ∧ check missingRoute good wire = false ∧
      check wrongIssuer good wire = false := by
  refine ⟨.forward (by decide +kernel),?_,by decide +kernel,by decide +kernel,by decide +kernel⟩
  exact (RecordTrail455.source_opener_iff_finite_original_index455 ..).mp ⟨1,by decide +kernel⟩

#print axioms same_raw_alias_and_native_origin_do_not_replace_the_authored_route455

#print axioms routed_branch_actual_program_has_full_fit455
#print axioms routed_branch_depth_three_gives_same_model455
#print axioms routed_cyclic_variable_sibling_is_never_an_inspection455

end Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.Spec
