import Yulang.GeneralDeclarativeI65I74RoutedRecordEntry455

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
namespace Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.NonfirstSpec
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

def twoRealArms : Pattern :=
  .record 99 (chain 9 [50,51] (.var 31)) (branched f)

def firstWhere : Pattern := chain 9 [99] (.var 31)
def secondWhere : Pattern := chain 9 [10] (.var 3)

def writtenClause (used : Pattern) : GeneralDeclarations.Clause := ⟨6,19,[used],[]⟩
def originalImpl (used : Pattern) : Declaration :=
  ⟨218,19,[twoRealArms],[writtenClause used],[],[]⟩
def surface (form : Pattern) : InputBundle :=
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

def build (form : Pattern) (s : GeneralDeclarativeHead320.State) (srcs : List Origin)
    (routes : List GeneralDeclarativeI65.Alias := actualRoutes) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile (surface form)
  let env : Environment := ⟨0,0,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,[],srcs,routes⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)


def actualOuter : Expr := .record 99 (.variable 7) outer
def actualOuterTerm : TyTerm Nat := .record 99 (.var 7) outside
def firstOriginTerm : TyTerm Nat := .record 50 (.var 8) .emptyRecord
def firstDeeperTerm : TyTerm Nat := .record 51 (.var 6) .emptyRecord
def twoArmsRaw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[⟨0,actualOuter⟩,⟨1,.variable 11⟩,oneRow 11 20 2,oneRow 2 30 3,
    oneRow 3 40 3,oneRow 9 90 9,oneRow 7 50 8,oneRow 8 51 6]⟩
def armOrigins : List Origin :=
  [⟨0,[401],.ordinary actualOuterTerm⟩,⟨11,[402],.ordinary middle⟩,
    ⟨2,[403],.ordinary lastOpened⟩,⟨7,[404],.ordinary firstOriginTerm⟩,
    ⟨8,[405],.ordinary firstDeeperTerm⟩]

def completeInput : FullProblem :=
  (build firstWhere twoArmsRaw armOrigins).get (by decide +kernel)
def sameHeadOtherWhere : FullProblem :=
  (build secondWhere twoArmsRaw armOrigins).get (by decide +kernel)

def esc0 : ExactEscapeWire := ⟨List.range 12,[0,1,1,1,2,2,1,1,1,1,2,1]⟩
def esc1 : ExactEscapeWire := ⟨List.range 12,[2,0,1,1,2,2,2,2,2,2,2,0]⟩
def esc2 : ExactEscapeWire := ⟨List.range 12,[2,2,0,1,2,2,2,2,2,2,2,2]⟩

def nextPath : TrailWire tokenOps :=
  .down ⟨2,.forward 1,0,0,(1 : Nat)⟩ esc1
    (.down ⟨3,.same,0,0,(2 : Nat)⟩ esc2 .stop)
def activeTrail : TrailWire tokenOps := .down ⟨0,.same,1,1,(0 : Nat)⟩ esc0 nextPath
def wrongWritten : TrailWire tokenOps := .down ⟨0,.same,1,0,(0 : Nat)⟩ esc0 nextPath
def wrongObserved : TrailWire tokenOps := .down ⟨0,.same,0,1,(0 : Nat)⟩ esc0 nextPath
def cut : FieldCycleWire := ⟨⟨4,.same,3⟩,[],.same⟩
def wire : FieldWire := ⟨9,⟨activeTrail,cut⟩⟩
def good : FieldReport := ⟨[71,2],218,[(10,1),(20,2),(30,3)],3⟩
def accepted (p : FullProblem) (w : FieldWire) : Bool :=
  check_full455 p (.fieldK2 good) (.fieldK2 w)

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [accepted completeInput wire,
  accepted completeInput ⟨9,⟨wrongWritten,cut⟩⟩,
  accepted completeInput ⟨9,⟨wrongObserved,cut⟩⟩,
  accepted sameHeadOtherWhere wire]

def recursive (field : Nat) : Ty :=
  .record field (.block [.record field (.inl 0) .emptyRecord] 0) .emptyRecord

theorem recursive_unfold455 (field : Nat) :
    Equivalent (recursive field) (record field (recursive field) .emptyRecord) := by
  have both (depth : Nat) : CommonNominalFullCarrier.observeTy depth (recursive field) =
      CommonNominalFullCarrier.observeTy depth (record field (recursive field) .emptyRecord) := by
    cases depth <;> rfl
  constructor
  · intro depth; rw [←both depth]; exact CommonNominalFullDemand.producerLe_refl _
  · intro depth; rw [both depth]; exact CommonNominalFullDemand.producerLe_refl _

def ty2 : Ty := record 30 (recursive 40) .emptyRecord
def ty1 : Ty := record 20 ty2 .emptyRecord
def ty6 : Ty := .base .bool
def ty8 : Ty := record 51 ty6 .emptyRecord
def ty7 : Ty := record 50 ty8 .emptyRecord
def ty0 : Ty := record 99 ty7 (record 10 ty1 (record 90 (recursive 90) .emptyRecord))
def value (n : Nat) : Ty :=
  if n = 0 then ty0 else if n = 2 then ty2 else if n = 3 then recursive 40 else
    if n = 9 then recursive 90 else if n = 6 then ty6 else if n = 7 then ty7 else
      if n = 8 then ty8 else ty1

def model : I72.Model :=
  ⟨fun n => (value n,Common.rowEmpty),fun _ => none,fun n =>
    if n = 0 then some (.ordinary actualOuterTerm) else if n = 11 then some (.ordinary middle) else
      if n = 2 then some (.ordinary lastOpened) else if n = 7 then some (.ordinary firstOriginTerm) else
        if n = 8 then some (.ordinary firstDeeperTerm) else none⟩

theorem actual_nonfirst_field_uses_same_genuine_fitting_model455 :
    FitsFull completeInput.state model ∧ FieldEvidence completeInput.old model good := by
  have fit : FitsFull completeInput.state model := by
    refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
    · intro _ bad; cases bad
    · intro _ bad; cases bad
    · intro row inRows
      change row ∈ [⟨0,actualOuter⟩,⟨1,.variable 11⟩,oneRow 11 20 2,oneRow 2 30 3,
        oneRow 3 40 3,oneRow 9 90 9,oneRow 7 50 8,oneRow 8 51 6] at inRows
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inRows
      rcases inRows with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      all_goals first | exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _ |
        exact recursive_unfold455 40 | exact recursive_unfold455 90
    · intro _ bad; cases bad
    · intro o present
      change o ∈ armOrigins at present
      simp only [armOrigins,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl|rfl|rfl|rfl|rfl <;> rfl
    · intro _ bad; cases bad
  have isChecked : accepted completeInput wire = true := by decide +kernel
  exact ⟨fit,(check_full_sound455 completeInput (.fieldK2 good) (.fieldK2 wire) isChecked).2 model fit⟩

open GeneralDeclarationPatterns (CountsCovered Smaller ConservativeSmaller StableSmaller checkSmaller_exact)

theorem real_nonfirst_where_has_stable_counts_but_the_old_conservative_bound_fails455 :
    CountsCovered [twoRealArms] [secondWhere] ∧
      Smaller [twoRealArms] [secondWhere] ∧ StableSmaller [twoRealArms] [secondWhere] ∧
      ¬ ConservativeSmaller [twoRealArms] [secondWhere] := by
  have smaller := (checkSmaller_exact [twoRealArms] [secondWhere]).mp (by decide +kernel)
  have exactHead := (RecordTree455.checkTrees_exact 9 [twoRealArms]).mp (by decide +kernel)
  have exactBody := (RecordTree455.checkTrees_exact 9 [secondWhere]).mp (by decide +kernel)
  refine ⟨⟨rfl,rfl⟩,smaller,RecordTree455.written_tree_paterson_stable_under_all_captures455 exactHead exactBody smaller,?_⟩
  intro no
  cases no

theorem present_fixed_declaration_cannot_certify_that_nonfirst_where455
    (constructors : GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls) :
    ¬ GeneralDeclarations.DeclarationChecked constructors roles (originalImpl secondWhere) := by
  intro checked
  exact real_nonfirst_where_has_stable_counts_but_the_old_conservative_bound_fails455.2.2.2
    (checked.conservative _ List.mem_cons_self)

#print axioms actual_nonfirst_field_uses_same_genuine_fitting_model455
#print axioms real_nonfirst_where_has_stable_counts_but_the_old_conservative_bound_fails455
#print axioms present_fixed_declaration_cannot_certify_that_nonfirst_where455

end Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.NonfirstSpec
