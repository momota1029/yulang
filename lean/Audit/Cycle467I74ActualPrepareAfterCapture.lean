import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeWitnessNativePreparation360
import Yulang.GeneralDeclarativeWitnessNativeValue360
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65Heads367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C467ActualDeclarationOrdinal
open GeneralDeclarations (Declaration)
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def literalRoleRows (r offset : Nat) : List Declaration → List (Nat × Declaration)
  | [] => []
  | first::rest =>
    if first.role = r then (offset,first)::literalRoleRows r (offset+1) rest
    else literalRoleRows r (offset+1) rest

theorem role_row_erasure_is_the_existing_authored_filter (r offset : Nat) (table : List Declaration) :
    (literalRoleRows r offset table).map Prod.snd = table.filter (fun d => d.role == r) := by
  induction table generalizing offset with
  | nil => rfl
  | cons d ds ih =>
    by_cases wanted : d.role = r
    · simp [literalRoleRows,wanted,ih]
    · simp [literalRoleRows,wanted,ih]

private theorem literal_role_rows_lower {r off i : Nat} {table : List Declaration} {d : Declaration}
    (there : (i,d) ∈ literalRoleRows r off table) : off ≤ i := by
  induction table generalizing off with
  | nil => simp [literalRoleRows] at there
  | cons head rest lower =>
    by_cases here : head.role = r
    · simp only [literalRoleRows,here,ite_true,List.mem_cons] at there
      rcases there with front|later
      · exact Nat.le_of_eq (congrArg Prod.fst front).symm
      · have on := lower later
        omega
    · simp [literalRoleRows,here] at there
      have on := lower there
      omega

theorem literal_role_rows_record_exact_unfiltered_ordinals
    (r offset : Nat) (table : List Declaration) (i : Nat) (d : Declaration) :
    (offset+i,d) ∈ literalRoleRows r offset table ↔ table[i]? = some d ∧ d.role = r := by
  induction table generalizing offset i with
  | nil => simp [literalRoleRows]
  | cons d₀ later ih =>
    cases i with
    | zero =>
      have noTail : (offset,d) ∉ literalRoleRows r (offset+1) later := by
        intro wrong
        have x := literal_role_rows_lower wrong
        omega
      by_cases here : d₀.role = r
      · simp [literalRoleRows,here,noTail]
        constructor
        · intro eq
          exact ⟨eq.symm,eq ▸ here⟩
        · intro eq
          exact eq.1.symm
      · simp [literalRoleRows,here,noTail]
        intro eq same
        exact here (eq.symm ▸ same)
    | succ i =>
      have off : offset + (i+1) = offset+1+i := by omega
      have noHead : (offset + (i+1),d) ≠ (offset,d₀) := by
        intro eq
        have bad := congrArg Prod.fst eq
        simp at bad
      by_cases here : d₀.role = r
      · simp only [literalRoleRows,here,ite_true,List.mem_cons,noHead,false_or,
          List.getElem?_cons_succ]
        rw [off]
        exact ih _ _
      · simp only [literalRoleRows,here,ite_false,List.getElem?_cons_succ]
        rw [off]
        exact ih _ _

def originalHeadOrdinal {p : Problem} (h : OriginalHead p) : Option Nat :=
  match literalRoleRows p.root.demand.role 0 p.state.core.current.environment.source.declarations with
  | [(i,d)] => if d = h.declaration then some i else none
  | _ => none

theorem a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index
    {p : Problem} (h : OriginalHead p)
    (one : (visible p.state.core p.root).length = 1) :
    ∃ i, originalHeadOrdinal h = some i ∧
      p.state.core.current.environment.source.declarations[i]? = some h.declaration ∧
      ∀ j, p.state.core.current.environment.source.declarations[j]? = some h.declaration → j = i := by
  let decls := p.state.core.current.environment.source.declarations
  let kept := literalRoleRows p.root.demand.role 0 decls
  have eq : kept.map Prod.snd = visible p.state.core p.root :=
    role_row_erasure_is_the_existing_authored_filter .. 
  have length : kept.length = 1 := by
    have h := congrArg List.length eq
    rw [List.length_map,one] at h
    exact h
  obtain ⟨⟨i,d⟩,only⟩ := List.length_eq_one_iff.mp length
  have declared : h.declaration = d := by
    rw [only] at eq
    have atVisible := h.actualVisible
    rw [←eq] at atVisible
    have mem := List.mem_of_getElem? atVisible
    exact List.mem_singleton.mp mem
  subst d
  have found : (0+i,h.declaration) ∈ literalRoleRows p.root.demand.role 0 decls := by
    change (0+i,h.declaration) ∈ kept
    simp [only]
  have real := (literal_role_rows_record_exact_unfiltered_ordinals _ _ _ _ _).mp found
  refine ⟨i,?_,real.1,?_⟩
  · unfold originalHeadOrdinal
    have exactTable : literalRoleRows p.root.demand.role 0 decls = [(i,h.declaration)] := only
    change literalRoleRows p.root.demand.role 0 p.state.core.current.environment.source.declarations = [(i,h.declaration)] at exactTable
    rw [exactTable]
    simp
  · intro j equation
    have mem := (literal_role_rows_record_exact_unfiltered_ordinals _ 0 decls j h.declaration).mpr ⟨equation,real.2⟩
    have exactPair : (j,h.declaration) = (i,h.declaration) := by
      change (0+j,h.declaration) ∈ kept at mem
      simpa [only] using mem
    exact congrArg Prod.fst exactPair

open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared)

def actualCompilerFrameKey {p : Problem} (h : OriginalHead p) : Option FrameKey :=
  (originalHeadOrdinal h).map fun i => ⟨p.root.occurrence,h.declaration.id,i⟩

theorem a_real_single_head_fixes_an_existing_prepared_frame_without_generating_authority
    {p : Problem} (h : OriginalHead p)
    (one : (visible p.state.core p.root).length = 1) :
    ∃ frame,
      actualCompilerFrameKey h = some frame ∧
      frame.occurrence = p.root.occurrence ∧
      frame.declaration = h.declaration.id ∧
      p.state.core.current.environment.source.declarations[frame.sourceOrdinal]? = some h.declaration ∧
      ∀ (layout : Layout) (existing : Prepared p.state.core.current.environment frame p.root.demand layout),
        existing.impl = h.declaration := by
  obtain ⟨i,at_i,sourceAt,_⟩ := a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index h one
  refine ⟨⟨p.root.occurrence,h.declaration.id,i⟩,?_,rfl,rfl,sourceAt,?_⟩
  · simp [actualCompilerFrameKey,at_i]
  · intro _ actual
    exact Option.some.inj (actual.authored.symm.trans sourceAt)

end Yulang.C467ActualDeclarationOrdinal


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual467PhaseBridge
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralSourceMetadataRows291 (Row)
open CommonNominalFullCarrier (Ty Equivalent record)
open Core.PresenceGeneration (TyTerm)
open AuthenticatedHop458 (Wire CycleWire)
open RecordK2412 (FieldCycleWire cycle_at_sound412)
open InlineStructuralPolicy458 (emptyPolicy)
open RoutedNominalPoint456 (cov)
open RetainedFull445 (FullProblem liftProblem)
open PreparedDeclarations463
open List410 (ExactEscapeWire)

private def empty : Expr := .primitive .emptyRecord []
private def mkNamed (x label child : Nat) : Equation := ⟨x,.record label (.variable child) empty⟩
private def rawSelf : Equation := mkNamed 5 40 5
private def inlineMid : Equation := ⟨6,.record 31 rawSelf.right empty⟩
private def inlineRoot : Equation := ⟨4,.record 30 inlineMid.right empty⟩
private def oldRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf]⟩

private def pattern : Pattern :=
  .record 30 (.record 31 (.var 3) (.app 9 [])) (.app 9 [])
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 syntax6 .emptyRecord
private def native : List Origin :=
  [⟨4,[402],.ordinary syntax4⟩,⟨6,[402],.ordinary syntax6⟩,⟨5,[402],.ordinary syntax5⟩]

private def pairAt (s : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← compile bodies
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  let auth ← GeneralSourceMetadataBareBundle291.compile
    ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[declaration]⟩
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,List.replicate 20 [] ++ [[cov]],native,[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

private def before : FullProblem := (pairAt oldRaw).get (by decide +kernel)

private theorem ready : DeclarationReady (authoredRegistry before.old.state.core.current) declaration := by
  have bits : RecordTrail455.localAuthorBits before.old.state.core.current.environment declaration = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp bits
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c absent
  cases absent

open Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose)

private def certified : CheckedTable before.state.base.core.current :=
  ⟨[declaration],fun _d mem => (List.mem_singleton.mp mem).symm ▸ ready⟩

private def legacySupport : Supported (ordinary before.old) (fun _ => False) :=
  ⟨fun e o => e ∈ oldRaw.equations ∧ o = .source,fun got => got.1⟩

private noncomputable def groundedRows : GeneralDeclarativeNestedView332.Sources (restriction legacySupport) :=
  ofRows oldRaw.equations (fun _ h => from_source _ ⟨h,rfl⟩)

private structure KeySummary where
  decl : Nat
  target : Nat
  raw : Nat
  occurrence : Nat
  path : List Pose
  binder : Nat
  deriving DecidableEq

private def reduced (found : CheckedCaptureHead before.old certified) : KeySummary :=
  ⟨found.original.orig.declaration.id,found.allocated.target,found.allocated.rawOrdinal,
    found.allocated.captureOrdinal,found.allocated.written,found.allocated.captured.binder⟩

private noncomputable def accepted :=
  (readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0).map reduced

theorem actual_prechecked_native_request_has_the_exact_old_ordinary_capture_receipt :
    accepted = some ⟨218,7,3,0,[Pose.payload,Pose.payload],3⟩ := by
  decide +kernel

private def missingGD : CheckedTable before.state.base.core.current :=
  ⟨[],fun _ not => False.elim (List.not_mem_nil not)⟩
private def routable := ofRows (s := oldRaw) oldRaw.equations (fun _ h => h)

private def recState : CommonNominalSyntax.State Common.Row :=
  .block [.record 40 (.inl 0) .emptyRecord] 0
private def mu : Ty := .record 40 recState .emptyRecord
private theorem unfolded : Equivalent mu (record 40 mu .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k mu =
      CommonNominalFullCarrier.observeTy k (record 40 mu .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [← each]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each]
    exact CommonNominalFullDemand.producerLe_refl _

private def midTy := record 31 mu .emptyRecord
private def rootTy := record 30 midTy .emptyRecord
private def concrete : I72.Model :=
  ⟨fun n => (if n = 4 then rootTy else if n = 6 then midTy else mu,Common.rowEmpty),
    fun _ => none,
    fun n => if n = 4 then some (.ordinary syntax4)
      else if n = 6 then some (.ordinary syntax6)
      else if n = 5 then some (.ordinary syntax5) else none⟩

theorem actual_prechecked_input_with_capture_has_a_real_fitting_model :
    FitsFull before.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [inlineRoot,inlineMid,rawSelf] at row
    rcases List.mem_cons.mp row with rfl|row
    · change Equivalent (record 30 (record 31 mu .emptyRecord) .emptyRecord)
          (record 30 (record 31 (record 40 mu .emptyRecord) .emptyRecord) .emptyRecord)
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30
        (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · rcases List.mem_cons.mp row with rfl|row
      · change Equivalent (record 31 mu .emptyRecord) (record 31 (record 40 mu .emptyRecord) .emptyRecord)
        exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
      · obtain rfl := List.mem_singleton.mp row
        exact unfolded
  · intro _ bad; cases bad
  · intro source here
    change source ∈ native at here
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad


theorem original_input_has_no_native_origin_at_the_fresh_allocated_target :
    ∀ o ∈ before.state.base.core.origins, o.slot ≠ 7 := by
  intro o inside
  change o ∈ native at inside
  simp only [native,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl|rfl|rfl <;> decide

open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Alias321 (no_nonempty_alias_only)

private noncomputable def chosen :=
  readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0

private theorem realCaptureExists : chosen.isSome = true := by
  decide +kernel

private noncomputable def witness := chosen.get realCaptureExists

private def expectedAfter : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
    ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩]⟩

theorem genuine_compiler_adds_its_ordinary_row_but_not_all_named_graph_coordinates :
    witness.allocated.after = expectedAfter ∧
    witness.allocated.after.equations[3]? = some ⟨7,rawSelf.right⟩ ∧
    ∀ e ∈ witness.allocated.after.equations, e.left = 4 → shapeOf e.right = none := by
  have h : exactOrdinaryState witness.allocated.after expectedAfter = true := by
    decide +kernel
  have q := (exact_ordinary_snapshot_iff ..).mp h
  refine ⟨q,?_,?_⟩
  · rw [q]
    rfl
  · rw [q]
    intro e row owns
    change e ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
      ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at row
    simp only [List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with (rfl|rfl|rfl|rfl|rfl)
    · rfl
    · cases owns
    · cases owns
    · cases owns
    · rfl


open Yulang.C467ActualDeclarationOrdinal
open GeneralDeclarativeWitnessNativePreparation360 (Layout prepare Prepared)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)

private def inputRecipe (r : CheckedCaptureHead before.old certified) : Layout :=
  ⟨r.allocated.after,r.allocated.captures,[],fun _ => point 0,fun _ _ => 0⟩

private def printAtom : PresenceNormalForm.Atom Nat → Nat × Nat × Nat
  | .tyLe (.var l) (.var r) => (0,l,r)
  | .rowLe (.var l) (.var r) => (1,l,r)
  | _ => (2,0,0)

private def phaseStatus : Option (List Nat × Nat × Nat × List Nat × List (Nat × Nat) × List (Nat × Nat × Nat) × Bool) := do
  let capture ← readCaptureFromReadyHead before.old certified routable ⟨0,0⟩ [] 0
  let key ← actualCompilerFrameKey capture.original.orig
  let prepared ← GeneralDeclarativeWitnessNativePreparation360.prepare before.old.state.core.current.environment key before.old.root.demand (inputRecipe capture)
  pure (key.occurrence,key.declaration,key.sourceOrdinal,prepared.stage.equations.map Equation.left,prepared.stage.normal.intervals,prepared.stage.normal.ordinary.map printAtom,
    exactOrdinaryState prepared.stage capture.allocated.after)

private def captureRun :=
  readCaptureFromReadyHead before.old certified routable ⟨0,0⟩ [] 0
private theorem captureRunExists : captureRun.isSome = true := by decide +kernel
private def physicalCapture := captureRun.get captureRunExists
private def exactKey : FrameKey := ⟨[71,2],218,0⟩

private def prepareActual :=
  GeneralDeclarativeWitnessNativePreparation360.prepare before.old.state.core.current.environment exactKey
    before.old.root.demand (inputRecipe physicalCapture)
private theorem readyActualExists : prepareActual.isSome = true := by decide +kernel
private def genuine := prepareActual.get readyActualExists

private def atAtom (a b : Nat) : PresenceNormalForm.Atom Nat := .tyLe (.var a) (.var b)
private def actualArguments := [atAtom 7 7,atAtom 7 7,atAtom 8 7,atAtom 7 8,
  atAtom 9 7,atAtom 7 9,atAtom 8 7,atAtom 7 9]
private def expectedCurrent : GeneralDeclarativeHead320.State :=
  ⟨⟨actualArguments,[]⟩,expectedAfter.equations⟩

theorem actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase :
    actualCompilerFrameKey physicalCapture.original.orig = some exactKey ∧
    physicalCapture.allocated.after = expectedAfter ∧
    genuine.stage = expectedCurrent ∧
    genuine.stage ≠ physicalCapture.allocated.after := by
  have oldAfter := (exact_ordinary_snapshot_iff ..).mp
    (show exactOrdinaryState physicalCapture.allocated.after expectedAfter = true from by decide +kernel)
  have these := (exact_ordinary_snapshot_iff ..).mp
    (show exactOrdinaryState genuine.stage expectedCurrent = true from by decide +kernel)
  refine ⟨by decide +kernel,oldAfter,these,?_⟩
  rw [these,oldAfter]
  intro equality
  have lengths := congrArg (fun s : GeneralDeclarativeHead320.State => s.normal.ordinary.length) equality
  change 8 = 0 at lengths
  cases lengths

theorem this_actual_prepared_no_output_source_is_not_a_native360_emission_producer
    (wire : GeneralDeclarativeWitnessAssociatedDescriptor359.Wire) (version : Nat) :
    GeneralDeclarativeWitnessNativeValue360.compile genuine before.old.state.core.modes wire version = none := by
  cases compiled : GeneralDeclarativeWitnessNativeValue360.compile genuine before.old.state.core.modes wire version with
  | none => rfl
  | some result =>
    have asked := result.supplied.indexed
    change ([] : List GeneralSourceState.Output)[wire.ordinal]? = some result.supplied.requested at asked
    simp at asked

/-- info: some
  ([71, 2], 218, 0, [4, 6, 5, 7, 4], [],
    [(0, 7, 7), (0, 7, 7), (0, 8, 7), (0, 7, 8), (0, 9, 7), (0, 7, 9), (0, 8, 7), (0, 7, 9)], false) -/
#guard_msgs in
#eval phaseStatus

open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open CommonNominalFullCarrier (Subtype observeTy)
open CommonNominalFullDemand (Environment ProbeAt ProbeStep MaskedProbeStep producerLe_iff_probe probeAt_record_field)

private def alternate : Assignment :=
  fun n => if n = 8 then (.base .int,Common.rowEmpty) else concrete.assignment n

private theorem concreteFitsOldAssembled : Models expectedAfter concrete.assignment := by
  have pre := actual_prechecked_input_with_capture_has_a_real_fitting_model.1.1.1
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro e occurs
    change e ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
      ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at occurs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at occurs
    rcases occurs with (rfl|rfl|rfl|rfl|rfl)
    · exact pre.2 _ List.mem_cons_self
    · exact pre.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact pre.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact unfolded
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _

private theorem int_is_not_the_actually_captured_recursive_record : ¬ Subtype (.base .int) mu := by
  intro claim
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => []⟩
  have want : ProbeAt Common.rowLe 0 env (observeTy 0 mu) (.field 40 .trivial) := by
    change ProbeAt Common.rowLe 0 env (.record 40 _ .emptyRecord) (.field 40 .trivial)
    rw [probeAt_record_field]
    simp [ProbeAt,ProbeStep]
  have impossible := (producerLe_iff_probe _ _).mp (claim 0) 0 env (.field 40 .trivial) want
  change ProbeAt Common.rowLe 0 env (.base .int) (.field 40 .trivial) at impossible
  simp [ProbeAt,ProbeStep,MaskedProbeStep] at impossible

theorem real_actual_prepare_has_a_fitting_assignment_counterexample_to_phase_identity :
    Models physicalCapture.allocated.after alternate ∧ ¬ Models genuine.stage alternate := by
  have actual := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
  rw [actual.2.1,actual.2.2.1]
  have unchanged : ∀ n ∈ stateNames expectedAfter, concrete.assignment n = alternate n := by
    have not : 8 ∉ stateNames expectedAfter := by decide +kernel
    intro n gives
    have ne : n ≠ 8 := fun wrong => not (wrong ▸ gives)
    simp [alternate,ne]
  refine ⟨(preserves_models _ unchanged).mp concreteFitsOldAssembled,?_⟩
  intro bad
  have atom : atAtom 8 7 ∈ expectedCurrent.normal.ordinary := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have proof : Subtype (.base .int) mu := bad.1.1 _ atom
  exact int_is_not_the_actually_captured_recursive_record proof


theorem exact_new_phase_models_equal_old_plus_two_explicit_capture_coordinates
    (m : Assignment) :
    Models genuine.stage m ↔ Models physicalCapture.allocated.after m ∧
      Equivalent (m 8).1 (m 7).1 ∧ Equivalent (m 9).1 (m 7).1 := by
  have actual := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
  rw [actual.2.1,actual.2.2.1]
  constructor
  · intro ready
    refine ⟨⟨⟨?_,?_⟩,ready.2⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
    · intro _ gone
      cases gone
    · intro _ gone
      cases gone
    · exact ready.1.1 (atAtom 8 7) (by simp [expectedCurrent,actualArguments])
    · exact ready.1.1 (atAtom 7 8) (by simp [expectedCurrent,actualArguments])
    · exact ready.1.1 (atAtom 9 7) (by simp [expectedCurrent,actualArguments])
    · exact ready.1.1 (atAtom 7 9) (by simp [expectedCurrent,actualArguments])
  · rintro ⟨old,lo,hi⟩
    refine ⟨⟨?_,?_⟩,old.2⟩
    · intro atom mem
      change atom ∈ actualArguments at mem
      simp only [actualArguments,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      · exact CommonNominalFullCarrier.subtype_refl _
      · exact CommonNominalFullCarrier.subtype_refl _
      · exact lo.1
      · exact lo.2
      · exact hi.1
      · exact hi.2
      · exact lo.1
      · exact hi.2
    · intro _ gone
      cases gone

theorem actual_both_ordinary_phases_can_fit_one_model_with_new_coordinates_agreeing :
    Models physicalCapture.allocated.after concrete.assignment ∧ Models genuine.stage concrete.assignment := by
  have old := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase.2.1.symm ▸ concreteFitsOldAssembled
  exact ⟨old,(exact_new_phase_models_equal_old_plus_two_explicit_capture_coordinates _).mpr
    ⟨old,GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _,
      GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _⟩⟩

def adjustFreshPhaseCoordinates (m : Assignment) : Assignment :=
  fun n => if n = 8 ∨ n = 9 then m 7 else m n

theorem any_old_ordinary_model_extends_to_actual_native_prepare_keeping_old_names
    (m : Assignment) (fitted : Models physicalCapture.allocated.after m) :
    Models genuine.stage (adjustFreshPhaseCoordinates m) ∧
      ∀ n ∈ stateNames physicalCapture.allocated.after,
        adjustFreshPhaseCoordinates m n = m n := by
  have old := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase.2.1
  have noEight : 8 ∉ stateNames physicalCapture.allocated.after := by rw [old]; decide +kernel
  have noNine : 9 ∉ stateNames physicalCapture.allocated.after := by rw [old]; decide +kernel
  have same : ∀ n ∈ stateNames physicalCapture.allocated.after,
      adjustFreshPhaseCoordinates m n = m n := by
    intro n ofOld
    have a : n ≠ 8 := fun h => noEight (h ▸ ofOld)
    have b : n ≠ 9 := fun h => noNine (h ▸ ofOld)
    simp [adjustFreshPhaseCoordinates,a,b]
  exact ⟨(exact_new_phase_models_equal_old_plus_two_explicit_capture_coordinates _).mpr
    ⟨(preserves_models _ same).mpr fitted,
      GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _,GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _⟩,same⟩



open GeneralDeclarativeBounds319 (Bound)

private theorem old_actual_bounds_are_reflexive {a b : Nat}
    (h : Bound expectedAfter.normal a b) : a = b := by
  induction h with
  | interval mem => cases mem
  | constraint mem => cases mem
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem old_actual_has_no_variable_rhs (a b : Nat) :
    (⟨a,.variable b⟩ : Equation) ∉ expectedAfter.equations := by
  intro h
  change (⟨a,.variable b⟩ : Equation) ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
      ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at h
  simp [inlineRoot,inlineMid,rawSelf,mkNamed,Equation.mk.injEq] at h

private theorem old_actual_aliases_are_reflexive {a b : Nat}
    (h : GeneralDeclarativeLowerKnown321.Alias expectedAfter a b) : a = b := by
  induction h with
  | bounds ab _ => exact old_actual_bounds_are_reflexive ab
  | forward h => exact False.elim (old_actual_has_no_variable_rhs _ _ h)
  | backward h => exact False.elim (old_actual_has_no_variable_rhs _ _ h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem exact_real_prepared_alias_changes_from_new_phase_bounds :
    GeneralDeclarativeLowerKnown321.Alias genuine.stage 8 7 ∧ GeneralDeclarativeLowerKnown321.Alias genuine.stage 9 7 ∧
      ¬ GeneralDeclarativeLowerKnown321.Alias physicalCapture.allocated.after 8 7 ∧
      ¬ GeneralDeclarativeLowerKnown321.Alias physicalCapture.allocated.after 9 7 := by
  have actual := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
  rw [actual.2.1,actual.2.2.1]
  refine ⟨?_,?_,?_,?_⟩
  · exact .bounds (.constraint (by decide +kernel)) (.constraint (by decide +kernel))
  · exact .bounds (.constraint (by decide +kernel)) (.constraint (by decide +kernel))
  · exact fun h => (by decide : (8 : Nat) ≠ 7) (old_actual_aliases_are_reflexive h)
  · exact fun h => (by decide : (9 : Nat) ≠ 7) (old_actual_aliases_are_reflexive h)


theorem real_native_prepare_changes_raw_constructor_knowledge_at_fresh_eight :
    GeneralDeclarativeLowerKnown321.Knows genuine.stage 8 (.record 40) ∧
      ∀ tag, ¬ GeneralDeclarativeLowerKnown321.Knows physicalCapture.allocated.after 8 tag := by
  have actual := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
  constructor
  · refine GeneralDeclarativeLowerKnown321.knows_alias exact_real_prepared_alias_changes_from_new_phase_bounds.1 ?_
    refine ⟨⟨7,rawSelf.right⟩,?_,GeneralDeclarativeLowerKnown321.alias_refl 7,rfl⟩
    rw [actual.2.2.1]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · intro tag
    rw [actual.2.1]
    rintro ⟨row,mem,link,_⟩
    have eq := old_actual_aliases_are_reflexive link
    change row ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
      ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with (rfl|rfl|rfl|rfl|rfl) <;> cases eq


open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeGraphRows321 (observed)

private theorem every_actual_ordinary_shape_only_points_to_five
    (s : GeneralDeclarativeHead320.State) (eqs : s.equations = expectedAfter.equations)
    {a b : Nat}
    (d : Descends (GeneralDeclarativeGraphRows321.structural s) a b) : b = 5 := by
  obtain ⟨shape,⟨owner,_alias,exp,mem,shapeEq⟩,child⟩ := d
  rw [eqs] at mem
  change (⟨owner,exp⟩ : Equation) ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
    ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  have transfer :
      ∀ row : Equation, (⟨owner,exp⟩ : Equation) = row →
        (GeneralDeclarativeGraphRows321.shapeOf row.right = some shape) := by
    intro row h
    have rn := congrArg Equation.right h
    rwa [← rn]
  rcases mem with h|h|h|h|h
  · have no := transfer _ h
    change none = some shape at no
    cases no
  · have no := transfer _ h
    change none = some shape at no
    cases no
  · have yes := transfer _ h
    change some (.record [(40,5)]) = some shape at yes
    cases yes
    simpa [GeneralDeclarativeK2Graph321.Shape.children] using child
  · have yes := transfer _ h
    change some (.record [(40,5)]) = some shape at yes
    cases yes
    simpa [GeneralDeclarativeK2Graph321.Shape.children] using child
  · have no := transfer _ h
    change none = some shape at no
    cases no

private theorem every_actual_ordinary_path_from_five_ends_at_five
    (s : GeneralDeclarativeHead320.State) (eqs : s.equations = expectedAfter.equations)
    {x y : Nat}
    (path : Path (GeneralDeclarativeGraphRows321.structural s) x y) : x = 5 → y = 5 := by
  induction path with
  | refl => exact id
  | next edge _ ih => exact fun _ => ih (every_actual_ordinary_shape_only_points_to_five s eqs edge)

private theorem new_actual_bounds_cannot_leave_five {a b : Nat}
    (h : Bound expectedCurrent.normal a b) :
    (a = 5 → b = 5) := by
  induction h with
  | interval mem => cases mem
  | @constraint x y mem =>
    intro a5
    subst x
    change atAtom 5 y ∈ actualArguments at mem
    simp [actualArguments,atAtom] at mem
  | refl => exact id
  | trans _ _ ih₁ ih₂ => exact fun eq => ih₂ (ih₁ eq)

private theorem new_actual_aliases_cannot_leave_five {a b : Nat}
    (h : GeneralDeclarativeLowerKnown321.Alias expectedCurrent a b) :
    a = 5 → b = 5 := by
  induction h with
  | bounds ab _ => exact new_actual_bounds_cannot_leave_five ab
  | forward h => exact False.elim (old_actual_has_no_variable_rhs _ _ h)
  | backward h => exact False.elim (old_actual_has_no_variable_rhs _ _ h)
  | trans _ _ ih₁ ih₂ => exact fun eq => ih₂ (ih₁ eq)

theorem actual_preparation_preserves_inhabited_raw_cycles_exactly_at_five
    (n : Nat) :
    (AliasCycle physicalCapture.allocated.after (observed physicalCapture.allocated.after) n ↔ n = 5) ∧
    (AliasCycle genuine.stage (observed genuine.stage) n ↔ n = 5) := by
  have actual := actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
  rw [actual.2.1,actual.2.2.1]
  have test (s : GeneralDeclarativeHead320.State) (eqs : s.equations = expectedAfter.equations)
      (only : ∀ a, GeneralDeclarativeLowerKnown321.Alias s 5 a → a = 5) :
      AliasCycle s (observed s) n ↔ n = 5 := by
    constructor
    · rintro ⟨child,last,next,path,back⟩
      have five := every_actual_ordinary_shape_only_points_to_five s eqs next
      have stop := every_actual_ordinary_path_from_five_ends_at_five s eqs path five
      subst last
      exact only _ back
    · rintro rfl
      refine ⟨5,5,?_,.refl _,GeneralDeclarativeLowerKnown321.alias_refl _⟩
      refine ⟨.record [(40,5)],⟨5,GeneralDeclarativeLowerKnown321.alias_refl _, rawSelf.right,?_,rfl⟩,?_⟩
      · rw [eqs]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · decide
  exact ⟨test _ rfl (fun _ h => (old_actual_aliases_are_reflexive h).symm),
    test _ rfl (fun _ h => new_actual_aliases_cannot_leave_five h rfl)⟩

#print axioms actual_preparation_preserves_inhabited_raw_cycles_exactly_at_five

#print axioms real_native_prepare_changes_raw_constructor_knowledge_at_fresh_eight

#print axioms exact_real_prepared_alias_changes_from_new_phase_bounds

#print axioms any_old_ordinary_model_extends_to_actual_native_prepare_keeping_old_names
#print axioms exact_new_phase_models_equal_old_plus_two_explicit_capture_coordinates
#print axioms actual_both_ordinary_phases_can_fit_one_model_with_new_coordinates_agreeing
#print axioms real_actual_prepare_has_a_fitting_assignment_counterexample_to_phase_identity
#print axioms actual_same_head_frame_and_ordinary_capture_do_not_give_literal_native_phase
#print axioms this_actual_prepared_no_output_source_is_not_a_native360_emission_producer
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual467PhaseBridge
