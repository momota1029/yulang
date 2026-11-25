import Yulang.GeneralDeclarativeI65I74MixedRecordRival413

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413.FiniteControl
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible SourceHead)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)
open RecordK2412 (closedWhere412 closedHead412 recordInput412 recordRow412)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def bindingOnly : Declaration := ⟨56,7,[closedWhere412 20 9 3],[],[],[]⟩
def bindingOther : Declaration := ⟨58,7,[closedWhere412 20 9 13],[],[],[]⟩
def inspecting : Declaration := ⟨57,7,[closedHead412 20 21 9 8],[],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

def outer : Equation := recordRow412 0 20 1
def cycle : Equation := recordRow412 1 21 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outer,cycle]⟩

def build (rows : List Declaration) (raw : GeneralDeclarativeHead320.State := ordinary) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨environment,raw,[]⟩,[],[⟨0,[22],recordInput412 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : MixedWire := ⟨⟨0,0,⟨[0,1],[0,1]⟩⟩,⟨⟨1,.same,1⟩,[],.same⟩⟩
def report : Result := Check408.rawReport
def checkOpt (p : Option Problem) (r : Result := report) (w : Witness := .mixedHead wire) : Bool :=
  (p.map fun data => check data r w).getD false

def normal := build [bindingOnly,inspecting]
def reversed := build [inspecting,bindingOnly]
def three := build [bindingOnly,inspecting,bindingOther]

def finiteField : Equation := recordRow412 1 21 2
def expanded : Equation :=
  ⟨0,.record 20 (.record 21 (.variable 2) (.primitive .emptyRecord [])) (.primitive .emptyRecord [])⟩
def leaf : Equation := ⟨2,.primitive .emptyRecord []⟩
def rawFinite : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outer,finiteField,expanded,leaf]⟩
def finite := build [bindingOnly,inspecting] rawFinite

def readyTape (p : Problem) :
    Option (Σ root : VerifiedOuter p, MixedTape root.actual (visible p.state.core p.root)) := do
  let root ← rootRead413 p ⟨0,0,⟨[0,1,1],[0,1]⟩⟩
  match ← scanAll413 root.actual (visible p.state.core p.root) with
  | .plain _ => none
  | .mixed tape => some ⟨root,tape⟩

def fullInputReady (p : Problem) : Bool := (readyTape p).isSome

theorem finite_control_has_the_real_full_matched_tape413 :
    (finite.map fullInputReady).getD false = true := by decide +kernel

theorem no_cycle_at_actual_finite_field413 :
    ¬GeneralDeclarativeK2Alias321.AliasCycle rawFinite
      (GeneralDeclarativeGraphRows321.observed rawFinite) 1 :=
  List410.exact_escape_refutes_raw_root_K2410 (w := ⟨[2,0,1],[0,1,2]⟩) (by decide +kernel)

theorem finite_context_is_exact413 {p : Problem} (built : finite = some p) :
    p.state.core.current.ordinary = rawFinite ∧
    p.state.core.origins = [⟨0,[22],recordInput412 20 1⟩] := by
  unfold finite build at built
  cases graph : compile bodies with
  | none => simp [graph] at built
  | some program =>
    cases source : GeneralSourceMetadataBareBundle291.compile
        (surface [bindingOnly,inspecting]) with
    | none => simp [graph,source] at built
    | some metadata =>
      simp only [graph,source,Option.pure_def] at built
      cases built
      exact ⟨rfl,rfl⟩

theorem no_witness_can_invent_a_cycle_in_the_same_finite_input413 {p : Problem} (built : finite = some p) :
    ∀ r w, check p r (.mixedHead w) = false := by
  intro r w
  cases run : check p r (.mixedHead w) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨packet,_,_⟩ := checked_mixed_head_reflects_original413 p r w run
    obtain ⟨actualGraph,origins⟩ := finite_context_is_exact413 built
    have member := packet.rejection.outer.actualOrigin
    rw [origins] at member
    have endpoint := packet.rejection.outer.originalTerm
    rw [List.mem_singleton.mp member] at endpoint
    change recordInput412 20 1 = recordInput412 packet.rejection.outer.box packet.rejection.outer.site at endpoint
    have site : packet.rejection.outer.site = 1 := by
      injection endpoint with term
      have field := (Core.PresenceGeneration.TyTerm.record.inj term).2.1
      exact (Core.PresenceGeneration.TyTerm.var.inj field).symm
    have cycle := packet.rejection.actualCycle
    rw [actualGraph,site] at cycle
    exact no_cycle_at_actual_finite_field413 cycle

def finiteTy : Ty := record 21 .emptyRecord .emptyRecord
def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 finiteTy .emptyRecord else if n = 1 then finiteTy else .emptyRecord),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem actual_finite_control_fits_without_vacuity413 {p : Problem} (ready : finite = some p) :
    I72.Fits p.state model := by
  unfold finite build at ready
  cases sem : compile bodies with
  | none => simp [sem] at ready
  | some program =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface [bindingOnly,inspecting]) with
    | none => simp [sem,source] at ready
    | some bundle =>
      simp only [sem,source,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro e member
        have choices : e = outer ∨ e = finiteField ∨ e = expanded ∨ e = leaf := by
          simpa only [rawFinite,List.mem_cons,List.not_mem_nil,or_false] using member
        rcases choices with rfl|rfl|rfl|rfl <;>
          exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
      · intro _ empty; cases empty
      · intro o exactOrigin
        obtain rfl := List.mem_singleton.mp exactOrigin
        rfl

open GeneralDeclarativeWitnessDeclaredState357 (point)
open CommonRoleOutermostResolver (All₂)
open RecordK2412 (query412)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem both_heads_genuinely_match_in_the_finite_control413 {p : Problem} (built : finite = some p) :
    Nonempty (SourceHead p.state.core p.root bindingOnly) ∧
      Nonempty (SourceHead p.state.core p.root inspecting) := by
  have ready := finite_control_has_the_real_full_matched_tape413
  simp only [built,Option.map_some,Option.getD_some,fullInputReady] at ready
  obtain ⟨raw,origins⟩ := finite_context_is_exact413 built
  have shape : visible p.state.core p.root = [bindingOnly,inspecting] ∧ p.root.demand.arguments = [point 0] := by
    unfold finite build at built
    cases program : compile bodies with
    | none => simp [program] at built
    | some graph =>
      cases already : GeneralSourceMetadataBareBundle291.compile (surface [bindingOnly,inspecting]) with
      | none => simp [program,already] at built
      | some bundle =>
        simp only [program,already,Option.pure_def] at built
        cases built
        refine ⟨?_,rfl⟩
        have metadata : bundle.declarations = [bindingOnly,inspecting] :=
          congrArg InputBundle.declarations (GeneralSourceMetadataBareBundle291.preserves_input _ _ already).1
        change bundle.declarations.filter (fun d => d.role == 7) = _
        rw [metadata]
        rfl
  cases got : readyTape p with
  | none => simp [got] at ready
  | some data =>
    let view := data.1.actual
    let tape : MixedTape view [bindingOnly,inspecting] := shape.1 ▸ data.2
    have atRoot : view.root = 0 := by
      have fact := (List.cons.inj (view.args.symm.trans shape.2)).1
      exact congrArg GeneralDeclarativeWhere319.Capture.lower fact
    have label : view.box = 20 := by
      have mem := view.actualOrigin
      rw [origins] at mem
      have endpoint := view.originalTerm
      rw [List.mem_singleton.mp mem] at endpoint
      injection endpoint with term
      exact (Core.PresenceGeneration.TyTerm.record.inj term).1.symm
    cases tape with
    | opens impos _ =>
      have impossible := impos.head
      change [closedWhere412 20 9 3] =
        [closedHead412 view.box impos.nextField impos.empty impos.binder] at impossible
      injection impossible with one
      have notPattern := (GeneralDeclarationPatterns.Pattern.record.inj one).2.1
      cases notPattern
    | next left right =>
      refine ⟨⟨left.matches⟩,?_⟩
      cases right with
      | next _ impossible => cases impossible
      | opens rigid _ =>
        have written := (List.cons.inj rigid.head).1
        change closedHead412 20 21 9 8 = closedHead412 view.box rigid.nextField rigid.empty rigid.binder at written
        have inner := (GeneralDeclarationPatterns.Pattern.record.inj written).2.1
        have tick := (GeneralDeclarationPatterns.Pattern.record.inj inner).1
        let capture : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 2
        refine ⟨.ordered capture ?_⟩
        rw [view.args,rigid.head]
        refine .cons (.ordinary ?_) .nil
        refine ⟨⟨.refl _,.refl _⟩,query412 view.box rigid.nextField rigid.binder,?_ , .direct (.whole ?_)⟩
        · exact rigid.compiled
        · rw [atRoot,label,←tick,raw]
          change expanded ∈ rawFinite.equations
          decide +kernel

theorem finite_same_input_has_two_real_matches_but_no_K2_certificate413 :
    ∃ p, finite = some p ∧ I72.Fits p.state model ∧
      Nonempty (SourceHead p.state.core p.root bindingOnly) ∧
      Nonempty (SourceHead p.state.core p.root inspecting) ∧
      ∀ r w, check p r (.mixedHead w) = false := by
  have tape := finite_control_has_the_real_full_matched_tape413
  cases yes : finite with
  | none => simp [yes] at tape
  | some p =>
    obtain ⟨a,b⟩ := both_heads_genuinely_match_in_the_finite_control413 yes
    exact ⟨p,rfl,actual_finite_control_fits_without_vacuity413 yes,a,b,
      no_witness_can_invent_a_cycle_in_the_same_finite_input413 yes⟩

#eval [(finite.map fullInputReady).getD false,checkOpt finite]
#print axioms finite_same_input_has_two_real_matches_but_no_K2_certificate413
#print axioms both_heads_genuinely_match_in_the_finite_control413
#print axioms finite_control_has_the_real_full_matched_tape413
#print axioms no_cycle_at_actual_finite_field413
#print axioms no_witness_can_invent_a_cycle_in_the_same_finite_input413
#print axioms actual_finite_control_fits_without_vacuity413
end Yulang.GeneralDeclarativeI65.I72.MixedRecord413.FiniteControl
