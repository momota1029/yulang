import Yulang.GeneralDeclarativeI65I74RoutedReadyMixedEntry457
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.RoutedReadyMixed457.CompositeSpec
open Yulang.GeneralDeclarativeI65
open RetainedFull445 RecordTraversal455
open RecordTrail455 (Form chain tokenOps)
open RecordTraversal455.MixedQA
open RoutedMixed456 (MixedReport FieldWire)
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
  .record 99 (chain 9 [50,51] (.var 31)) (.record 10 (.variant 7 (.app 8 [.var 88,.app 20 [chain f.empty f.writtenHead.tail (.var f.binder)]]))
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
def rows : List Equation := [⟨0,outer⟩,⟨1,.variable 11⟩,⟨11,.variant 7 (.variable 2)⟩,
  ⟨2,middlePair⟩,⟨3,.nominal 20 [.variable 4]⟩,oneRow 4 30 5,
  oneRow 5 40 5,oneRow 9 90 9,oneRow 7 50 8,oneRow 8 51 6]
def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,rows⟩
def outside : TyTerm Nat := .record 99 (.var 7) (.record 10 (.var 1) (.record 90 (.var 9) .emptyRecord))
def firstOpen : TyTerm Nat := .variant 7 (.var 2)
def secondOpen : TyTerm Nat := .pair (.var 9) (.var 3)
def thirdOpen := marker 20 4
def lastOpened : TyTerm Nat := .record 30 (.var 5) .emptyRecord
def beforeFirst : TyTerm Nat := .record 50 (.var 8) .emptyRecord
def atFirst : TyTerm Nat := .record 51 (.var 6) .emptyRecord
def origins : List Origin :=
  [⟨0,[401],.ordinary outside⟩,⟨11,[402],.ordinary firstOpen⟩,
    ⟨2,[403],.ordinary secondOpen⟩,⟨3,[404],thirdOpen⟩,⟨4,[405],.ordinary lastOpened⟩,
    ⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]
def rawMiddleOnly : List Origin :=
  [⟨0,[401],.ordinary outside⟩,⟨1,[402],.ordinary firstOpen⟩,
    ⟨2,[403],.ordinary secondOpen⟩,⟨3,[404],thirdOpen⟩,⟨4,[405],.ordinary lastOpened⟩,
    ⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]

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

def oldP : FullProblem := (build oldWhere raw origins).get (by decide +kernel)
def p : FullProblem := (build actualWhere raw origins).get (by decide +kernel)
def missingRoute : FullProblem := (build actualWhere raw origins []).get (by decide +kernel)
def wrongIssuer : FullProblem := (build actualWhere raw origins [⟨1,11,[777]⟩]).get (by decide +kernel)
def missingOwner : FullProblem := (build actualWhere raw rawMiddleOnly).get (by decide +kernel)
def capturedAt3 : FullProblem := (build (.var 650) raw origins).get (by decide +kernel)
def earlierRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [oneRow 1 88 1]}
def earlier : FullProblem := (build actualWhere earlierRaw origins []).get (by decide +kernel)
def parentRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨1,.variable 0⟩]}
def parentCycle : FullProblem := (build actualWhere parentRaw origins).get (by decide +kernel)

def badVariant : FullProblem := (build actualWhere raw
    [⟨0,[401],.ordinary outside⟩,⟨11,[402],.ordinary (.variant 17 (.var 2))⟩,
      ⟨2,[403],.ordinary secondOpen⟩,⟨3,[404],thirdOpen⟩,⟨4,[405],.ordinary lastOpened⟩,
    ⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]).get
    (by decide +kernel)
def badPairSecond : FullProblem := (build actualWhere raw
    [⟨0,[401],.ordinary outside⟩,⟨11,[402],.ordinary firstOpen⟩,
      ⟨2,[403],.ordinary (.pair (.var 9) (.var 2))⟩,⟨3,[404],thirdOpen⟩,⟨4,[405],.ordinary lastOpened⟩,
    ⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]).get
    (by decide +kernel)
def badNominal : FullProblem := (build actualWhere raw
    [⟨0,[401],.ordinary outside⟩,⟨11,[402],.ordinary firstOpen⟩,
      ⟨2,[403],.ordinary secondOpen⟩,⟨3,[404],marker 20 5⟩,⟨4,[405],.ordinary lastOpened⟩,
    ⟨7,[406],.ordinary beforeFirst⟩,⟨8,[407],.ordinary atFirst⟩]).get
    (by decide +kernel)

def escape (here : Nat) (atSame reached : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = here || atSame.contains i then 0 else if reached.contains i then 1 else 2⟩
def trail (pairIndex : Nat) : MixedWire tokenOps :=
  .down ⟨0,.same,(0 : Nat)⟩ (.field 1 1) (escape 0 [] [1,11,2,3,4,5,6,7,8,9])
    (.down ⟨2,.forward 1,(1 : Nat)⟩ .variant (escape 1 [11] [2,3,4,5,9])
      (.down ⟨3,.same,(2 : Nat)⟩ (.index pairIndex) (escape 2 [] [3,4,5,9])
        (.down ⟨4,.same,(3 : Nat)⟩ (.index 0) (escape 3 [] [4,5])
          (.down ⟨5,.same,(4 : Nat)⟩ (.field 0 0) (escape 4 [] [5]) .stop))))
def finalCycle : FieldCycleWire := ⟨⟨6,.same,5⟩,[],.same⟩
def wire (i : Nat := 1) : FieldWire := ⟨9,⟨trail i,finalCycle⟩⟩
def good : ReportAtField := ⟨[71,2],218,0,6,
  [(.field 10,1),(.variant 7,2),(.primitive .pair 1,3),(.nominal 20 0,4),(.field 30,5)],5⟩
def check (p : FullProblem) (r : ReportAtField) (wstring : FieldWire) : Bool :=
  check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 wstring)

def inheritedRecord : MixedReport := ⟨[71,2],218,good.path,good.terminal⟩
def validPrior (p : FullProblem) : Bool :=
  check_full_ready_mixed457 p
    (.previous (.previous (.fieldK2 inheritedRecord)))
    (.previous (.previous (.fieldK2 (wire 1))))

def badWhere := (build (.var 650) raw origins).get (by decide +kernel)
def noFieldCycle : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations.take 6 ++ raw.equations.drop 7}
def pNoCycle := (build actualWhere noFieldCycle origins).get (by decide +kernel)

/-- info: [true, true, false, false, false, false, false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [check p good (wire 1), validPrior oldP, validPrior p, check oldP good (wire 1),
   check p good (wire 0),check missingRoute good (wire 1),check wrongIssuer good (wire 1),
   check badVariant good (wire 1),check badPairSecond good (wire 1),check badNominal good (wire 1),
   check p {good with terminal := 9} (wire 1),check p {good with originalClauseId := 7} (wire 1),
   check pNoCycle good (wire 1),check badWhere good (wire 1)]

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
def ty3 : Ty := nominal 20 [.inl ty4]
def ty2 : Ty := pair (mu 90) ty3
def ty1 : Ty := variant 7 ty2
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
    | 11 => some (.ordinary firstOpen)
    | 2 => some (.ordinary secondOpen)
    | 3 => some thirdOpen
    | 4 => some (.ordinary lastOpened)
    | 7 => some (.ordinary beforeFirst)
    | 8 => some (.ordinary atFirst)
    | _ => none⟩

theorem exact_nonfirst_mixed_path_uses_a_real_fit457 : FitsFull p.state model := by
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
    rcases real with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

theorem exact_nonfirst_full_five_edge_diagnosis457 : FieldEvidence p.old model good := by
  have passed : check p good (wire 1) = true := by decide +kernel
  exact (check_full_sound457 p (.fieldK2 good) (.fieldK2 (wire 1)) passed).2 model
    exact_nonfirst_mixed_path_uses_a_real_fit457

#print axioms exact_nonfirst_mixed_path_uses_a_real_fit457
#print axioms exact_nonfirst_full_five_edge_diagnosis457
theorem original_mixed_second_binder_is_ready_but_not_old_conservative457 :
    visible p.state.base.core p.root = [originalImpl actualWhere] ∧
    (RoutedReadyHeader457.readReadyHeader p.old
      (RoutedNominalMixed456.actualQueryDecoder p.state.base.core)
      (originalImpl actualWhere) (by decide +kernel) 9).isSome = true ∧
    RoutedReadyRecord457.outsideConservative (originalImpl actualWhere).head (clause actualWhere).arguments = true ∧
    (RoutedQueryHeader456.readHeader p.old (RoutedNominalMixed456.actualQueryDecoder p.state.base.core)
      (originalImpl actualWhere) (by decide +kernel) 9).isSome = false := by
  decide +kernel

#print axioms original_mixed_second_binder_is_ready_but_not_old_conservative457
end Yulang.GeneralDeclarativeI65.I72.RoutedReadyMixed457.CompositeSpec
