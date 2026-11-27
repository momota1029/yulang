import Yulang.GeneralDeclarativeI65I74RoutedReadyRecordEntry457

set_option maxHeartbeats 5000000
namespace Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.NonfirstBoundary457Spec
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

open RecordDiagnosticReady457
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)

theorem actual_nonfirst_where_passes_the_existing_declaration_ready_route456 :
    GeneralDeclarativeWitnessClassifyVariance357.DeclarationReady
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry
        sameHeadOtherWhere.state.base.core.current) (originalImpl secondWhere) := by
  have replay : checkDiagnosticReady sameHeadOtherWhere.state.base.core.current
      (originalImpl secondWhere) (writtenClause secondWhere) 9 = true := by decide +kernel
  exact actual_closed_header_supplies_prior_declaration_ready457
    ((genuine_local_header_checks_the_same_authored_scope457 rfl).mp replay)

theorem actual_nonfirst_local_ready_is_not_a_change_to_fixed_header456 :
    checkDiagnosticReady sameHeadOtherWhere.state.base.core.current
      (originalImpl secondWhere) (writtenClause secondWhere) 9 = true ∧
    (readHeader sameHeadOtherWhere.old (originalImpl secondWhere) (by decide +kernel) 9).isSome = false :=
  ⟨by decide +kernel,by decide +kernel⟩

#print axioms actual_nonfirst_where_passes_the_existing_declaration_ready_route456
#print axioms actual_nonfirst_local_ready_is_not_a_change_to_fixed_header456


open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarationPatterns (normalize)
open RecordTrail455 (routedOps independent_routed_trail_observes_same_model455 ModelTrail)

def exactWrittenQuery : Option Expr :=
  let s := sameHeadOtherWhere.state.base.core.current
  translate (authoredRegistry s).constructors (interpretation s.environment.source.snapshot) (normalize twoRealArms)

def readWithoutConservativeWhere : Option (TrailPath × Nat) := do
  let q ← exactWrittenQuery
  let s := sameHeadOtherWhere.state.base.core
  readCycleVisit s.current.ordinary (routedOps s) 0 q (liftCursor s wire.cursor)

theorem same_original_nonfirst_route_compares_without_where_read456 :
    readWithoutConservativeWhere = some (good.fieldPath,3) ∧
    visible sameHeadOtherWhere.state.base.core sameHeadOtherWhere.root = [originalImpl secondWhere] ∧
    accepted sameHeadOtherWhere wire = false := by decide +kernel

theorem genuine_second_where_unchanged_full_fit456 : FitsFull sameHeadOtherWhere.state model := by
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

theorem the_local_nonfirst_route_has_exact_same_model_authority456 :
    ∃ q, exactWrittenQuery = some q ∧
      ModelTrail sameHeadOtherWhere.state.base.core model 0 q good.fieldPath 3 := by
  let s := sameHeadOtherWhere.state.base.core
  have existing : exactWrittenQuery.isSome = true := by decide +kernel
  let q := exactWrittenQuery.get existing
  have actual : exactWrittenQuery = some q := rfl
  have opened : readCycleVisit s.current.ordinary (routedOps s) 0 q (liftCursor s wire.cursor) =
      some (good.fieldPath,3) := by
    simpa [readWithoutConservativeWhere,actual,Option.bind,s] using
      same_original_nonfirst_route_compares_without_where_read456.1
  have loop := read_cycle_visit_sound455 opened
  exact ⟨q,actual,independent_routed_trail_observes_same_model455 loop.1 model
    genuine_second_where_unchanged_full_fit456.1⟩

#print axioms same_original_nonfirst_route_compares_without_where_read456
#print axioms genuine_second_where_unchanged_full_fit456
#print axioms the_local_nonfirst_route_has_exact_same_model_authority456


theorem actual_nonfirst_where_header_replay_uses_same_resolved_candidate456 :
    (RoutedReadyHeader457.readReadyHeader sameHeadOtherWhere.old
      (RoutedNominalMixed456.actualQueryDecoder sameHeadOtherWhere.state.base.core)
      (originalImpl secondWhere) (by decide +kernel) 9).isSome = true := by
  decide +kernel
#print axioms actual_nonfirst_where_header_replay_uses_same_resolved_candidate456

def readyReport : RoutedReadyRecord457.FieldReport := ⟨[71,2],218,0,6,[(10,1),(20,2),(30,3)],3⟩

def checkReady (p : FullProblem) (r : RoutedReadyRecord457.FieldReport := readyReport)
    (w : FieldWire := wire) : Bool :=
  RoutedReadyRecord457.check_full457 p (.fieldK2 r) (.fieldK2 w)

def checkInherited (p : FullProblem) : Bool :=
  RoutedReadyRecord457.check_full457 p
    (.previous (.previous (.previous (.fieldK2 good))))
    (.previous (.previous (.previous (.fieldK2 wire))))

def safeTerminal : GeneralDeclarativeHead320.State :=
  {twoArmsRaw with equations := twoArmsRaw.equations.take 4 ++ twoArmsRaw.equations.drop 5}
def missingCycle : FullProblem :=
  (build secondWhere safeTerminal armOrigins).get (by decide +kernel)
def wrongIssuer : FullProblem :=
  (build secondWhere twoArmsRaw armOrigins [⟨1,11,[999]⟩]).get (by decide +kernel)
def missingRoute : FullProblem :=
  (build secondWhere twoArmsRaw armOrigins []).get (by decide +kernel)
def badScope : FullProblem :=
  (build (.var 650) twoArmsRaw armOrigins).get (by decide +kernel)

/-- info: [true, true, false, false, false, false, false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [checkReady sameHeadOtherWhere,checkInherited completeInput,
   checkInherited sameHeadOtherWhere,checkReady completeInput,
   checkReady missingCycle,checkReady wrongIssuer,checkReady missingRoute,checkReady badScope,
   checkReady sameHeadOtherWhere {readyReport with originalClauseId := 7},
   checkReady sameHeadOtherWhere {readyReport with originalClauseOrdinal := 1},
   checkReady sameHeadOtherWhere {readyReport with terminal := 9},
   checkReady sameHeadOtherWhere {readyReport with declaration := 219},
   checkReady sameHeadOtherWhere readyReport ⟨9,⟨wrongWritten,cut⟩⟩,
   checkReady sameHeadOtherWhere readyReport ⟨9,⟨wrongObserved,cut⟩⟩]

theorem same_nonfirst_ready_is_a_field_diagnosis_in_same_fit457 :
    RoutedReadyRecord457.FieldEvidence sameHeadOtherWhere.old model readyReport := by
  exact (RoutedReadyRecord457.check_full_sound457 sameHeadOtherWhere (.fieldK2 readyReport) (.fieldK2 wire)
      (by decide +kernel)).2 model genuine_second_where_unchanged_full_fit456

theorem same_ready_without_terminal_cycle_cannot_be_a_field_report457 :
    (RoutedReadyHeader457.readReadyHeader missingCycle.old
      (RoutedNominalMixed456.actualQueryDecoder missingCycle.state.base.core)
      (originalImpl secondWhere) (by decide +kernel) 9).isSome = true ∧
    ¬ GeneralDeclarativeK2Alias321.AliasCycle safeTerminal
      (GeneralDeclarativeGraphRows321.observed safeTerminal) 3 ∧ checkReady missingCycle = false := by
  refine ⟨by decide +kernel,?_,by decide +kernel⟩
  exact checked_split_escape_excludes_exact_raw_K2446 (w := ⟨List.range 12,
    [2,2,2,0,2,2,2,2,2,2,2,2]⟩) (by decide +kernel)

#print axioms same_nonfirst_ready_is_a_field_diagnosis_in_same_fit457
#print axioms same_ready_without_terminal_cycle_cannot_be_a_field_report457

end Yulang.GeneralDeclarativeI65.I72.RoutedRecord455.NonfirstBoundary457Spec
