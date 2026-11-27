import Yulang.GeneralDeclarativeI65I74PreparedHeadField463
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeI65I74AuthenticCapturedStability462
import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462
import Yulang.GeneralDeclarativeI65I74FiniteCaptureBoundary462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.WholeReadBoundary463
open Yulang.GeneralDeclarativeI65
open RetainedFull445 RecordTraversal455
open RecordTrail455 (Form chain tokenOps)
open RecordTraversal455.MixedQA
open RoutedReadyMixed457 (ReportAtField)
open AuthenticatedHop458 (Wire)
open InlineStructuralPolicy458 (Ticket emptyPolicy)
open RoutedNominalPoint456
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent record nominal variant pair)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open List410 (ExactEscapeWire)
open RecordK2412 (FieldCycleWire)
open GeneralDeclarativeWitnessDeclaredState357 (point)

def bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
def f : Form := ⟨9,3,[10,30,40],[10]⟩
def badShallow : Form := ⟨9,3,[10,30],[10]⟩
def branched (f : Form) : Pattern :=
  .record 99 (chain 9 [50,51] (.var 31)) (.record 10 (.app 20 [.app 8 [.var 88,.variant 7 (chain f.empty f.writtenHead.tail (.var f.binder))]])
    (.record 90 (.var 99) (.app f.empty [])))

def oldWhere : Pattern := chain 9 [99] (.var 31)
def actualWhere : Pattern := chain 9 [10] (.var 3)
def clause (body : Pattern) : GeneralDeclarations.Clause := ⟨6,19,[body],[]⟩
def originalImpl (body : Pattern) : Declaration :=
  ⟨218,19,[branched f],[clause body],[],[]⟩
def surface (body : Pattern) : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,
    ⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[originalImpl body]⟩

def empty : Expr := .primitive .emptyRecord []
def outer : Expr := .record 99 (.variable 7) (.record 10 (.variable 1) (.record 90 (.variable 9) empty))
def oneRow (i field child : Nat) : Equation := ⟨i,.record field (.variable child) empty⟩

def middlePair : Expr := .primitive .pair [.variable 9,.variable 3]
def rows : List Equation := [⟨0,outer⟩,⟨1,.variable 11⟩,⟨11,.nominal 20 [.variable 2]⟩,
  ⟨2,middlePair⟩,⟨3,.variant 7 (.variable 4)⟩,oneRow 4 30 5,
  oneRow 5 40 5,oneRow 9 90 9,oneRow 7 50 8,oneRow 8 51 6]
def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,rows⟩
def outside : TyTerm Nat := .record 99 (.var 7) (.record 10 (.var 1) (.record 90 (.var 9) .emptyRecord))
def terminalTerm : TyTerm Nat := .record 40 (.var 5) .emptyRecord
def lastOpened : TyTerm Nat := .record 30 terminalTerm .emptyRecord
def thirdOpen : TyTerm Nat := .variant 7 lastOpened
def secondOpen : TyTerm Nat := .pair (.var 9) thirdOpen
def firstOpen := InlineNominalPoint458.marker 20 secondOpen
def beforeFirst : TyTerm Nat := .record 50 (.var 8) .emptyRecord
def atFirst : TyTerm Nat := .record 51 (.var 6) .emptyRecord
def origins : List Origin :=
  [⟨0,[401],.ordinary outside⟩,⟨11,[402],firstOpen⟩,
    ⟨2,[402],.ordinary secondOpen⟩,⟨3,[402],.ordinary thirdOpen⟩,⟨4,[402],.ordinary lastOpened⟩,
    ⟨5,[402],.ordinary terminalTerm⟩,⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]

def actualRoutes : List GeneralDeclarativeI65.Alias := [⟨1,11,[402]⟩]

def build (form : Pattern) (s : GeneralDeclarativeHead320.State) (srcs : List Origin)
    (routes : List GeneralDeclarativeI65.Alias := actualRoutes)
    (table : CommonDeclaredNominalInspection.Registry := List.replicate 20 [] ++ [[cov]]) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile (surface form)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,table,srcs,routes⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)

def p : FullProblem := (build actualWhere raw origins).get (by decide +kernel)
def wrongLastIssuer : FullProblem := (build actualWhere raw
  (origins.take 5 ++ [⟨5,[403],.ordinary terminalTerm⟩] ++ origins.drop 6)).get (by decide +kernel)
def wrongWrittenPair : FullProblem := (build actualWhere raw
  (origins.take 2 ++ [⟨2,[402],.ordinary (.pair (.var 8) thirdOpen)⟩] ++ origins.drop 3)).get (by decide +kernel)
def noFieldCycle : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations.take 6 ++ raw.equations.drop 7}
def terminalGone := (build actualWhere noFieldCycle origins).get (by decide +kernel)

def escape (here : Nat) (atSame reached : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = here || atSame.contains i then 0 else if reached.contains i then 1 else 2⟩
def trail (pairIndex fieldIndex : Nat) : Wire emptyPolicy :=
  .down ⟨0,.same,.field 1 1,(.older (.old 0) : Ticket)⟩ (escape 0 [] [1,11,2,3,4,5,6,7,8,9])
    (.down ⟨2,.forward 1,.index 0,(.nominal ⟨1,2,.same⟩ : Ticket)⟩ (escape 1 [11] [2,3,4,5,9])
      (.down ⟨3,.same,.index pairIndex,(.pair ⟨2,3,.same⟩ : Ticket)⟩ (escape 2 [] [3,4,5,9])
        (.down ⟨4,.same,.variant,(.older (.variantInline ⟨3,4,.same⟩) : Ticket)⟩ (escape 3 [] [4,5])
          (.down ⟨5,.same,.field 0 0,(.field ⟨4,5,fieldIndex,.same⟩ : Ticket)⟩ (escape 4 [] [5]) .stop))))
def finalCycle : FieldCycleWire := ⟨⟨6,.same,5⟩,[],.same⟩
def wire (i : Nat := 1) (j : Nat := 0) : FieldWire := ⟨9,⟨trail i j,finalCycle⟩⟩
def good : ReportAtField := ⟨[71,2],218,0,6,
  [(.field 10,1),(.nominal 20 0,2),(.primitive .pair 1,3),(.variant 7,4),(.field 30,5)],5⟩
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

def ty4 : Ty := record 30 (mu 40) .emptyRecord
def ty3 : Ty := variant 7 ty4
def ty2 : Ty := pair (mu 90) ty3
def ty1 : Ty := nominal 20 [.inl ty2]
def ty6 : Ty := .base .bool
def ty8 : Ty := record 51 ty6 .emptyRecord
def ty7 : Ty := record 50 ty8 .emptyRecord
def ty0 : Ty := record 99 ty7 (record 10 ty1 (record 90 (mu 90) .emptyRecord))
def assign (x : Nat) : Ty :=
  match x with
  | 0 => ty0 | 1 | 11 => ty1 | 2 => ty2 | 3 => ty3 | 4 => ty4
  | 5 => mu 40 | 6 => ty6 | 7 => ty7 | 8 => ty8 | 9 => mu 90 | _ => .base .int
def model : I72.Model :=
  ⟨fun n => (assign n,Common.rowEmpty),fun _ => none,fun n =>
    match n with
    | 0 => some (.ordinary outside)
    | 11 => some firstOpen
    | 2 => some (.ordinary secondOpen)
    | 3 => some (.ordinary thirdOpen)
    | 4 => some (.ordinary lastOpened)
    | 5 => some (.ordinary terminalTerm)
    | 7 => some (.ordinary beforeFirst)
    | 8 => some (.ordinary atFirst)
    | _ => none⟩

theorem actual_four_inline_forms_use_one_full_fit458 : FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r seen
    change r ∈ rows at seen
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    all_goals try exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact unfold_mu455 40
    · exact unfold_mu455 90
  · intro _ bad; cases bad
  · intro src real
    change src ∈ origins at real
    simp only [origins,List.mem_cons,List.not_mem_nil,or_false] at real
    rcases real with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

def identicalTag : Pattern := .variant 7 (chain 9 [30,40] (.var 3))
def originalHeadWithDuplicate : Pattern :=
  .record 99 (chain 9 [50,51] (.var 31))
    (.record 10 (.app 20 [.app 8 [.var 88,.join identicalTag identicalTag]])
      (.record 90 (.var 99) (.app 9 [])))
def duplicateImpl : Declaration := {originalImpl actualWhere with head := [originalHeadWithDuplicate]}

def buildFromVisibleDeclaration (d : Declaration) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    {surface actualWhere with declarations := [d]}
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,raw,[]⟩,List.replicate 20 [] ++ [[cov]],origins,actualRoutes⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 0],[]⟩⟩⟩)

def pDup : FullProblem := (buildFromVisibleDeclaration duplicateImpl).get (by decide +kernel)

def originalHeadWithThreeTags : Pattern :=
  .record 99 (chain 9 [50,51] (.var 31))
    (.record 10 (.app 20 [.app 8 [.var 88,.join identicalTag (.join identicalTag identicalTag)]])
      (.record 90 (.var 99) (.app 9 [])))
def tripleImpl : Declaration := {duplicateImpl with head := [originalHeadWithThreeTags]}
def pTriple : FullProblem := (buildFromVisibleDeclaration tripleImpl).get (by decide +kernel)

open CapturedNormalForm462
open EligibleFieldStart461
open WrittenPattern460
open InstalledProtocolSum462
open GeneralDeclarationPatterns (normalize StableSmaller)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)

-- The second written field 10 is already hidden by the first. The
-- authored source keeps it, along with the two distinct tag payloads.
def forwardWhere : Pattern :=
  .record 10 (.var 3)
    (.record 10 (.join (.variant 23 (.var 3)) (.variant 24 (.var 3))) (.app 9 []))

def withWrittenShadow : Declaration := originalImpl forwardWhere
def q : FullProblem := (buildFromVisibleDeclaration withWrittenShadow).get (by decide +kernel)

open PreparedDeclarations463 PhysicalVisit463 WrittenPattern460
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeI65 (SourceHead)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (shapeOf observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open CommonRoleOutermostResolver (All₂)
open RecordK2412 (checkCycleAt412 cycle_at_sound412)

def written : Pattern :=
  .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])
def writtenCode : Expr := .record 30 (.record 40 (.variable 3) empty) empty
def physicallyInline : Equation := ⟨4,.record 30 (.record 40 (.variable 5) empty) empty⟩
def terminalRow : Equation := oneRow 5 40 5
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physicallyInline,terminalRow]⟩
def onlyDecl : Declaration := ⟨218,19,[written],[],[],[]⟩

def sourceOnlyInline : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    {surface actualWhere with declarations := [onlyDecl]}
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,inlineRaw,[]⟩,List.replicate 20 [] ++ [[cov]],
    [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

def inlined : FullProblem := sourceOnlyInline.get (by decide +kernel)
def actualCap : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 5

theorem actual_written_closed_record_is_an_ordinary_source_head463 :
    Nonempty (SourceHead inlined.old.state.core inlined.old.root onlyDecl) := by
  refine ⟨.ordered actualCap (.cons (.ordinary ?_) .nil)⟩
  refine ⟨⟨Bound.refl _,Bound.refl _⟩,writtenCode,?_,.direct (.whole ?_)⟩
  · rfl
  · exact List.mem_cons_self

theorem actual_inline_source_model_fits_without_named_parent_row463 :
    FitsFull inlined.state model := by
  have fit := actual_four_inline_forms_use_one_full_fit458
  refine ⟨⟨⟨⟨fit.1.1.1.1,?_⟩,?_⟩,?_⟩,?_⟩
  · intro row found
    change row ∈ [physicallyInline,terminalRow] at found
    rcases List.mem_cons.mp found with rfl | found
    · change Equivalent (record 30 (mu 40) .emptyRecord)
          (record 30 (record 40 (mu 40) .emptyRecord) .emptyRecord)
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30 (unfold_mu455 40) (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · obtain rfl := List.mem_singleton.mp found
      exact fit.1.1.1.2 _ (by decide +kernel)
  · intro _ none
    cases none
  · intro src present
    change src ∈ [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩] at present
    rcases List.mem_cons.mp present with rfl | found
    · rfl
    · obtain rfl := List.mem_singleton.mp found
      rfl
  · intro _ none
    cases none

private theorem raw_bound_is_refl {a b : Nat} (d : Bound inlineRaw.normal a b) : a = b := by
  induction d with
  | interval mem => cases mem
  | constraint mem => cases mem
  | refl => rfl
  | trans _ _ i j => exact i.trans j

private theorem raw_alias_is_refl {a b : Nat}
    (d : GeneralDeclarativeLowerKnown321.Alias inlineRaw a b) : a = b := by
  induction d with
  | bounds h _ => exact raw_bound_is_refl h
  | forward h =>
    change _ ∈ [physicallyInline,terminalRow] at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · have h := List.mem_singleton.mp h
      cases h
  | backward h =>
    change _ ∈ [physicallyInline,terminalRow] at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · have h := List.mem_singleton.mp h
      cases h
  | trans _ _ i j => exact i.trans j

theorem no_existing_raw_open_at_actual_inline_parent463 {query : Expr} {k addr child next mark}
    (opens : IndexedOpen inlineRaw (InlineStructuralPolicy458.policy inlined.old.state.core)
      4 query k addr child next mark) : False := by
  obtain ⟨row,shape,stored,alias,compiled,_,_⟩ := opens.actual
  have read := List.mem_of_getElem? stored
  change row ∈ [physicallyInline,terminalRow] at read
  rcases List.mem_cons.mp read with rfl | remaining
  · change none = some shape at compiled
    cases compiled
  · obtain rfl := List.mem_singleton.mp remaining
    have impossible : (4 : Nat) = 5 := raw_alias_is_refl alias
    cases impossible

theorem descendant_cycle_is_real_but_it_cannot_supply_a_parent_visit463 :
    AliasCycle inlineRaw (observed inlineRaw) 5 ∧
      ∀ (w : HeadFieldWire inlined.old) tab, readHeadField (p := inlined.old) tab w = none := by
  refine ⟨cycle_at_sound412 (w := ⟨⟨1,.same,5⟩,[],.same⟩) (by decide +kernel),?_⟩
  intro w tab
  cases read : readHeadField (p := inlined.old) tab w with
  | none => rfl
  | some r =>
    exfalso
    have precise := (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨w,read⟩
    obtain ⟨a,last,_,trail,field,cycle,lit⟩ := precise
    have sharedArg : a.orig.capture = point 4 := by
      have occurs := List.mem_of_getElem? a.orig.actualArgument
      change a.orig.capture ∈ [point 4] at occurs
      exact List.mem_singleton.mp occurs
    have indices : a.orig.capture.lower = 4 := congrArg GeneralDeclarativeWhere319.Capture.lower sharedArg
    have strict : r.path ≠ [] := by
      intro nil
      rw [nil] at field
      simp [RoutedMixed456.endsAtField] at field
    rw [indices] at trail
    have cannot {t e path rows last final used}
        (actual : IndexedJoint inlineRaw (InlineStructuralPolicy458.policy inlined.old.state.core)
           (fun _ => queryKeys inlined.old.state.core) 4 t e path rows last final used) : path = [] := by
      cases actual with
      | stop => rfl
      | down _ opens _ _ => exact (no_existing_raw_open_at_actual_inline_parent463 opens).elim
    exact strict (cannot trail)


theorem actual_checked_declaration_is_ready_even_in_inline_only_state463 :
    DeclarationReady (authoredRegistry inlined.old.state.core.current) onlyDecl := by
  have exact : RecordTrail455.localAuthorBits inlined.old.state.core.current.environment onlyDecl = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp exact
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c appears
  cases appears

def inlinePreparedProtocol : CertificateProtocol inlined.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = onlyDecl)
  sound := fun _ _ chosen => (of_decide_eq_true chosen).symm ▸
    actual_checked_declaration_is_ready_even_in_inline_only_state463

def preparedInlineTable := (prepareTable inlinePreparedProtocol [(onlyDecl,())]).get (by decide +kernel)

theorem exact_inline_candidate_is_really_prechecked463 :
    (readPrecheckedHead (p := inlined.old) preparedInlineTable ⟨0,0⟩).isSome = true := by
  decide +kernel

#print axioms actual_checked_declaration_is_ready_even_in_inline_only_state463
#print axioms exact_inline_candidate_is_really_prechecked463
#print axioms actual_written_closed_record_is_an_ordinary_source_head463
#print axioms actual_inline_source_model_fits_without_named_parent_row463
#print axioms no_existing_raw_open_at_actual_inline_parent463
#print axioms descendant_cycle_is_real_but_it_cannot_supply_a_parent_visit463
end Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.WholeReadBoundary463
