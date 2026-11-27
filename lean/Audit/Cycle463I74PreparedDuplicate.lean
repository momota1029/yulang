import Yulang.GeneralDeclarativeI65I74PreparedLiteralFit463
import Yulang.GeneralDeclarativeI65I74AuthenticCapturedStability462
import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462
import Yulang.GeneralDeclarativeI65I74FiniteCaptureBoundary462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.PreparedDuplicate463
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

open PreparedDeclarations463
open WrittenPattern460.PhysicalOrigin
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (Smaller checkSmaller_exact)

private theorem test_decl_has_its_literal_where : withWrittenShadow.requirements = [clause forwardWhere] := rfl

-- Regression-only verifier for one real declaration in this exact
-- snapshot, not a GD completeness claim. It runs before any request.
def testVerifier : CertificateProtocol q.state.base.core.current where
  Data := Nat
  verify d key := decide (d = withWrittenShadow) &&
    verifiesStable key d.head (clause forwardWhere).arguments
  sound := by
    intro d key yes
    have cut := (Bool.and_eq_true ..).mp yes
    have eq : d = withWrittenShadow := of_decide_eq_true cut.1
    subst d
    have authored : RecordTrail455.localAuthorBits q.old.state.core.current.environment withWrittenShadow = true := by
      decide +kernel
    obtain ⟨covered,sig,id,prod,only,lex⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp authored
    have support := (finite_projected_stability_check_exact ..).mp cut.2
    refine ⟨sig,id,prod,only,lex,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl covered,?_⟩
    intro c chosen
    have same : c = clause forwardWhere := List.mem_singleton.mp chosen
    subst c
    refine ⟨?_,projection_transfers_original_all_captures key _ _ support⟩
    obtain ⟨_,_,_,_,_,_,strict⟩ := support
    exact strict

def made := prepareTable testVerifier [(withWrittenShadow,(9 : Nat))]
def actualTable := made.get (by decide +kernel)
def input : Input := ⟨q,actualTable⟩

def reqWire (i : Input) (address : AnchorAddress := ⟨0,0,0⟩)
    (raw : FieldWire := wire 1) : PreparedWire i :=
  ⟨address,(onOldCursor i.problem.old .plain raw.emptyKey raw.cursor).along⟩

def withBothOriginals : Declaration := {withWrittenShadow with head := [originalHeadWithDuplicate]}
def pBoth : FullProblem := (buildFromVisibleDeclaration withBothOriginals).get (by decide +kernel)

def onceBoth : CertificateProtocol pBoth.state.base.core.current where
  Data := Nat
  verify d key := decide (d = withBothOriginals) &&
    verifiesStable key d.head (clause forwardWhere).arguments
  sound := by
    intro d key yes
    have cut := (Bool.and_eq_true ..).mp yes
    have eq : d = withBothOriginals := of_decide_eq_true cut.1
    subst d
    have authored : RecordTrail455.localAuthorBits pBoth.old.state.core.current.environment withBothOriginals = true := by
      decide +kernel
    obtain ⟨covered,sig,id,prod,only,lex⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp authored
    have support := (finite_projected_stability_check_exact ..).mp cut.2
    refine ⟨sig,id,prod,only,lex,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl covered,?_⟩
    intro c chosen
    have same : c = clause forwardWhere := List.mem_singleton.mp chosen
    subst c
    refine ⟨?_,projection_transfers_original_all_captures key _ _ support⟩
    obtain ⟨_,_,_,_,_,_,strict⟩ := support
    exact strict

def both := prepareTable onceBoth [(withBothOriginals,(9 : Nat))]
def dual : Input := ⟨pBoth,both.get (by decide +kernel)⟩

def paths : List (List Pose) :=
  [[.tail,.payload,.app 0,.app 1,.left,.variant,.payload],
    [.tail,.payload,.app 0,.app 1,.right,.variant,.payload]]

def dualResult : Option (ReportAtField × Bool × List Nat × List (List Pose)) :=
  (readLocated (reqWire dual)).map fun l => (l.report,l.mark,l.equations,l.literal.map Prod.fst)

/-- info: [true, true, false, false, false] -/
#guard_msgs in
#eval [both.isSome,decide (dualResult = some (good,true,[0,2,3,4,5],paths)),
  decide (dualResult = some (good,true,[0,2,3,4,5],paths.reverse)),
  decide (dualResult = some (good,true,[0,2,3,4,5],paths.take 1)),
  decide (dualResult = some (good,true,[0,1,3,4,5],paths))]

theorem actual_two_originals_keep_exactly_the_same_raw_snapshot_and_fit463 :
    dual.problem.state.base.core.current.ordinary = input.problem.state.base.core.current.ordinary ∧
      FitsFull dual.problem.state model := by
  refine ⟨rfl,⟨actual_four_inline_forms_use_one_full_fit458.1,?_⟩⟩
  intro _ empty
  cases empty

theorem same_raw_route_replays_ordered_distinct_literal_positions463 :
    dualResult = some (good,true,[0,2,3,4,5],paths) := by decide +kernel

#print axioms actual_two_originals_keep_exactly_the_same_raw_snapshot_and_fit463
#print axioms same_raw_route_replays_ordered_distinct_literal_positions463
end Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.PreparedDuplicate463
