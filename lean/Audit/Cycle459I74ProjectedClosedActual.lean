import Yulang.GeneralDeclarativeI65I74ProjectedClosedEntry459
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.ProjectedClosed459Spec
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
def check (p : FullProblem) (r : ReportAtField := good) (w : FieldWire := wire) : Bool :=
  check_full_structural458 p (.fieldK2 r) (.fieldK2 w)

/-- info: [true, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [check p,check wrongLastIssuer,check wrongWrittenPair,check terminalGone,
  check p good (wire 0 0),check p good (wire 1 1),check p {good with terminal := 9},
  check p {good with originalClauseId := 7}]

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

theorem actual_four_inline_forms_prove_exact_field_report458 : FieldEvidence p.old model good := by
  have passed : check p = true := by decide +kernel
  exact (check_full_sound458 p (.fieldK2 good) (.fieldK2 (wire 1)) passed).2 model
    actual_four_inline_forms_use_one_full_fit458


#print axioms actual_four_inline_forms_use_one_full_fit458
#print axioms actual_four_inline_forms_prove_exact_field_report458


open GeneralDeclarationPatterns (normalize normalizeArgs substArgs counted)
open RecordTree455 (checkTree checkTrees)
open RoutedReadyHeader457 (readReadyHeader)
open RoutedNominalMixed456 (actualQueryDecoder)

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

theorem identical_tag_proof_under_every_capture458 (capture : Nat → Pattern) :
    normalize (originalHeadWithDuplicate.subst capture) =
      normalize ((branched f).subst capture) := by
  simp [originalHeadWithDuplicate,branched,f,identicalTag,GeneralDeclarationPatterns.Pattern.subst,
    substArgs,normalize,normalizeArgs,GeneralDeclarationPatterns.merge]

theorem duplicate_stable_counts_exact458 (capture : Nat → Pattern) :
    counted (substArgs capture duplicateImpl.head) =
      counted (substArgs capture (originalImpl actualWhere).head) := by
  change GeneralDeclarationPatterns.encodeArgs
      [normalize (originalHeadWithDuplicate.subst capture)] =
    GeneralDeclarationPatterns.encodeArgs [normalize ((branched f).subst capture)]
  rw [identical_tag_proof_under_every_capture458]

theorem authored_duplicate_has_exact_same_normalized_head458 :
    normalize originalHeadWithDuplicate = normalize (branched f) := by
  decide +kernel

theorem authored_duplicate_source_is_real_same_raw_fit458 :
    visible pDup.state.base.core pDup.root = [duplicateImpl] ∧ FitsFull pDup.state model := by
  refine ⟨by decide +kernel,?_⟩
  have old := actual_four_inline_forms_use_one_full_fit458
  refine ⟨⟨old.1.1,?_⟩,?_⟩
  · intro src actual
    change src ∈ origins at actual
    simp only [origins,List.mem_cons,List.not_mem_nil,or_false] at actual
    rcases actual with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

theorem authored_duplicate_header_key_never_removes_written_join458 (key : Nat) :
  checkTrees key duplicateImpl.head = false := by
  simp [duplicateImpl,originalHeadWithDuplicate,checkTrees,checkTree]


theorem exact_duplicate_report_current_no_wire458 (w : FieldWire) :
    check pDup good w = false := by
  cases accepted : check pDup good w
  · rfl
  · exfalso
    have gives : checkField pDup.old good w = true := accepted
    obtain ⟨a,_⟩ := (actual_routed_field_report_iff_finite_wire458 ..).mp ⟨w,gives⟩
    have same := List.singleton_inj.mp (a.source.only.symm.trans
      authored_duplicate_source_is_real_same_raw_fit458.1)
    have goodTree := (RecordTree455.checkTrees_exact ..).mpr a.source.admissibleHead
    rw [congrArg Declaration.head same,authored_duplicate_header_key_never_removes_written_join458] at goodTree
    cases goodTree

open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (Smaller StableSmaller)
open RecordTrail455 (localAuthorBits local_author_bits_exact455)

theorem exact_approved_duplicate_keeps_real_declaration_stability458 :
    DeclarationReady (authoredRegistry pDup.state.base.core.current) duplicateImpl := by
  have originalSelected : checkField p.old good (wire 1) = true := by decide +kernel
  obtain ⟨actual,_⟩ := (actual_routed_field_report_iff_finite_wire458 ..).mp ⟨_,originalSelected⟩
  have originalVisible :
      visible p.state.base.core p.root = [originalImpl actualWhere] := by decide +kernel
  have exactId := List.singleton_inj.mp (actual.source.only.symm.trans originalVisible)
  have oldDecl := RoutedReadyHeader457.read_ready_supplies_already_established_declaration_ready457 actual.source
  rw [exactId] at oldDecl
  have checked : localAuthorBits pDup.state.base.core.current.environment duplicateImpl = true := by
    decide +kernel
  obtain ⟨cover,sig,id,produced,only,scope⟩ := (local_author_bits_exact455 ..).mp checked
  refine ⟨sig,id,produced,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro chosen atChosen
  have wasChosen : chosen ∈ (originalImpl actualWhere).requirements := atChosen
  obtain ⟨localSmall,stable⟩ := oldDecl.descent chosen wasChosen
  refine ⟨?_,?_⟩
  · have sameCount : counted duplicateImpl.head = counted (originalImpl actualWhere).head := by
      decide +kernel
    unfold Smaller
    rw [sameCount]
    exact localSmall
  · intro capture
    unfold Smaller
    rw [duplicate_stable_counts_exact458 capture]
    exact stable capture

#print axioms exact_duplicate_report_current_no_wire458
#print axioms exact_approved_duplicate_keeps_real_declaration_stability458

#print axioms identical_tag_proof_under_every_capture458
#print axioms duplicate_stable_counts_exact458
#print axioms authored_duplicate_has_exact_same_normalized_head458
#print axioms authored_duplicate_source_is_real_same_raw_fit458

open IdenticalTagProjection459 (checkProjectedHeader projected_header_is_finite_exact459
  projected_header_proves_actual_original_ready459)

def differentSameTag : Pattern := .variant 7 (chain 9 [30,41] (.var 3))
def headWithNonidenticalTag : Pattern :=
  .record 99 (chain 9 [50,51] (.var 31))
    (.record 10 (.app 20 [.app 8 [.var 88,.join identicalTag differentSameTag]])
      (.record 90 (.var 99) (.app 9 [])))
def nonidenticalImpl : Declaration := {duplicateImpl with head := [headWithNonidenticalTag]}
def pNonidentical : FullProblem :=
  (buildFromVisibleDeclaration nonidenticalImpl).get (by decide +kernel)

theorem actual_projected_header_is_precise_for_duplicate_source458 :
    visible pNonidentical.state.base.core pNonidentical.root = [nonidenticalImpl] ∧
    checkProjectedHeader pDup.state.base.core.current duplicateImpl (clause actualWhere) 9 = true ∧
    checkProjectedHeader pNonidentical.state.base.core.current nonidenticalImpl (clause actualWhere) 9 = false := by
  decide +kernel

theorem actual_projected_header_produces_genuine_unchanged_declaration_ready458 :
    DeclarationReady (authoredRegistry pDup.state.base.core.current) duplicateImpl := by
  exact projected_header_proves_actual_original_ready459
    ((projected_header_is_finite_exact459 rfl).mp actual_projected_header_is_precise_for_duplicate_source458.2.1)

theorem actual_duplicate_retains_same_original_decoded_query458 :
    (actualQueryDecoder pDup.state.base.core).decode (normalize originalHeadWithDuplicate) =
      (actualQueryDecoder p.state.base.core).decode (normalize (branched f)) := by
  rw [authored_duplicate_has_exact_same_normalized_head458]
  rfl

#print axioms actual_projected_header_is_precise_for_duplicate_source458
#print axioms actual_projected_header_produces_genuine_unchanged_declaration_ready458
#print axioms actual_duplicate_retains_same_original_decoded_query458


def projectedWire (w : FieldWire := wire 1) : ProjectedClosedEntry459.FieldWire := ⟨w.emptyKey,w.cursor⟩

def replayProjected (q : FullProblem) (r : ReportAtField := good) (w : FieldWire := wire 1) :=
  ProjectedClosedEntry459.check_full_projected459 q (.fieldK2 r) (.fieldK2 (projectedWire w))

def priorReport (q : FullProblem) : Bool :=
  ProjectedClosedEntry459.check_full_projected459 q (.previous (.fieldK2 good)) (.previous (.fieldK2 (wire 1)))

theorem identical_duplicate_does_not_change_any_full_fit459 (m : I72.Model) :
    FitsFull pDup.state m ↔ FitsFull p.state m := by
  constructor <;> intro fit <;> refine ⟨⟨fit.1.1,fit.1.2⟩,?_⟩ <;> (intro _ absent; cases absent)

theorem exact_original_duplicate_reports_its_actual_raw_terminal459 :
    pDup.root = p.root ∧ pDup.state.base.core.current.ordinary = p.state.base.core.current.ordinary ∧
      pDup.state.base.core.origins = p.state.base.core.origins ∧ replayProjected pDup = true :=
  ⟨rfl,rfl,rfl,by decide +kernel⟩

theorem original_duplicate_keeps_same_model_evidence459 :
    ProjectedClosedEntry459.FieldEvidence pDup.old model good :=
  (ProjectedClosedEntry459.check_full_sound459 _ _ _ exact_original_duplicate_reports_its_actual_raw_terminal459.2.2.2).2
    model authored_duplicate_source_is_real_same_raw_fit458.2

theorem original_duplicate_exact_report_is_independent_and_finitely_replayed459 :
    ProjectedClosedEntry459.ExactField pDup.old good ∧
      ∃ result, ProjectedClosedEntry459.check_full_projected459 pDup (.fieldK2 good) (.fieldK2 result) = true := by
  have accepted := exact_original_duplicate_reports_its_actual_raw_terminal459.2.2.2
  have exact := (ProjectedClosedEntry459.check_full_sound459 _ _ _ accepted).1
  exact ⟨exact,ProjectedClosedEntry459.independent_routed_field_derivation_has_cumulative_witness459 _ _ exact⟩

/-- info: [true, false, false, true, false, false, false, false, false] -/
#guard_msgs in
#eval [replayProjected pDup,replayProjected pNonidentical,replayProjected p,priorReport p,priorReport pDup,
  replayProjected pDup good (wire 0 0),replayProjected pDup {good with terminal := 9},
  replayProjected pDup {good with originalClauseId := 7},replayProjected pDup good (wire 1 1)]

#print axioms identical_duplicate_does_not_change_any_full_fit459
#print axioms exact_original_duplicate_reports_its_actual_raw_terminal459
#print axioms original_duplicate_keeps_same_model_evidence459
#print axioms original_duplicate_exact_report_is_independent_and_finitely_replayed459

end Yulang.GeneralDeclarativeI65.I72.RoutedInlineStructural458.ProjectedClosed459Spec
