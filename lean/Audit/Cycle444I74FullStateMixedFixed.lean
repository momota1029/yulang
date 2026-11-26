import Yulang.GeneralDeclarativeI65I74MixedFixedRead442
import Yulang.GeneralDeclarativeI65I74FullState444

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442.FullStateExample444
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal point authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarationPatterns (normalize)
open CommonRecursiveNominalIntervals (Endpoint)
open CommonNominalFullCarrier (Ty nominal Equivalent subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open PresenceNormalForm (Atom)
open Checker408 (Problem)
open RefPositions441 (pattern layout endpoint)

def projectedRun : Source 3 1 1 :=
  ⟨[⟨9,[(.row,1),(.value,0)]⟩],
    fun i => match i.val with
    | 0 => .arrow (.inl 1) .empty (.inl 2) (.var 0)
    | 1 => .arrow (.inr 0) .empty (.inr 0) .empty
    | _ => .base .unit,
    fun p => if p.val = 1 then 0 else 1⟩

def out : GeneralDeclarations.Equation := ⟨100,76,pattern 9 6 8⟩
def declaration : Declaration := ⟨81,7,[pattern 9 6 8],[],[out],[]⟩
def catalogue (ds : List Declaration := [declaration]) : InputBundle :=
  let ctors : List Row := [⟨9,some ⟨[.row,.type],9⟩,.unclassified⟩,
    ⟨20,some ⟨[],20⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,ctors⟩,⟨.absent,ctors⟩,⟨0,[⟨7,1,[(76,none)]⟩]⟩,ds⟩

def makeEnv (ds : List Declaration := [declaration]) : Option Environment := do
  let graph ← compile projectedRun
  let book ← GeneralSourceMetadataBareBundle291.compile (catalogue ds)
  pure ⟨3,1,1,projectedRun,graph,book⟩

def env := (makeEnv).get (by decide +kernel)
def intRow : Equation := ⟨2,.primitive (.scalar .int) []⟩
def rowOne : Atom Nat := .rowLe (.var 1) (.var 1)
def valueTwo : Atom Nat := .tyLe (.var 2) (.var 2)

def originalView : AuthoredNominal := ⟨21,4,9,[.row (.var 1),.value (.var 2)]⟩
def inputOrigin : Origin := ⟨0,[71,3],endpoint 9 1 2⟩
def outputObservation : Origin := ⟨21,[71,3],endpoint 9 1 2⟩

def core (e : Environment := env) : GeneralDeclarativeI65.State :=
  ⟨⟨e,⟨⟨[rowOne,valueTwo],[]⟩,[intRow]⟩,[originalView]⟩,
    List.replicate 9 [] ++ [layout],[inputOrigin,outputObservation],[]⟩

def originalUse : Use (core).current.environment 9 2 :=
  (readUse (core).current.environment 9 2).get (by decide +kernel)

theorem mode : names originalUse.mode 2 = some layout := by decide +kernel
def originalPlan : B6MixedRhs401 (core) false (normalize (bodyPattern (.explicit out))) :=
  refPlan 9 6 8 originalUse mode rfl

def atlas : B6OccurrenceAtlas401 (core) := ⟨fun q o i body =>
  if q.occurrence == [71,3] && o == 0 && i.val == 0 then
    if h : body = .explicit out then some (h.symm ▸ originalPlan) else none
  else none⟩

def problem : Problem := ⟨⟨core,atlas⟩,⟨[71,3],⟨7,[point 0],[⟨76,21⟩]⟩⟩⟩
def wire : RefPositions441.Wire := ⟨0,⟨[0,1,2],[0,1,1]⟩⟩

theorem original_mixed_associated_source_replays442 :
    (replay442 problem wire).isSome = true := by decide +kernel

def replayed := (replay442 problem wire).get original_mixed_associated_source_replays442
def i0 : Fin problem.root.demand.outputs.length := ⟨0,by decide⟩
def named := replayed.event.outputs i0

theorem replayed_exact_original_fields442 :
    replayed.event.frame.decl = declaration ∧ replayed.event.frame.ordinal = 0 ∧
    replayed.event.frame.input 6 = point 1 ∧ replayed.event.frame.input 8 = point 2 ∧
    replayed.event.kids = [] ∧ named.receipt.occurrence = [71,3] ∧
    named.receipt.outputOrdinal = 0 ∧ named.receipt.original = ⟨76,21⟩ ∧
    named.body = .explicit out := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def effect : Common.Row := fun o => o = (56,[1,-2])
def refAt (r : Common.Row) : Ty := nominal 9 [.inr r,.inl (.base .int)]

def model (inputEffect targetEffect : Common.Row) (otherEffect : Common.Row := Common.rowEmpty) : I72.Model where
  assignment := fun n =>
    (if n = 21 then refAt targetEffect else if n = 22 then refAt otherEffect else .base .int,
     if n = 1 then inputEffect else Common.rowEmpty)
  authoredValues := fun n =>
    if n = 21 then some ⟨4,9,[.inr inputEffect,.inl (.base .int)]⟩ else none
  nativeSyntax := fun n => if n = 0 ∨ n = 21 then some (endpoint 9 1 2) else none

theorem every_input_and_target_row_fits442 (inputEffect targetEffect : Common.Row)
    (otherEffect : Common.Row := Common.rowEmpty) :
    I72.Fits problem.state (model inputEffect targetEffect otherEffect) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a present
    change a ∈ [rowOne,valueTwo] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl
    · exact Common.rowLe_refl _
    · exact subtype_refl _
  · intro e none
    cases none
  · intro eq present
    change eq ∈ [intRow] at present
    cases List.mem_singleton.mp present
    exact eqv_refl _
  · intro a present
    change a ∈ [originalView] at present
    cases List.mem_singleton.mp present
    exact ⟨⟨4,9,[.inr inputEffect,.inl (.base .int)]⟩,rfl,rfl,rfl,rfl⟩
  · intro a present
    change a ∈ [inputOrigin,outputObservation] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> rfl

theorem actual_replay_has_signed_mixed_value_at_original_target442 (x y : Common.Row) :
    named.receipt.actualEquation (model x y) = some (21,refAt x) := rfl

theorem same_ref_type_requires_same_row442 (r s : Common.Row) :
    Equivalent (refAt r) (refAt s) → r = s := by
  intro eq
  have shape := (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp eq.1
  exact shape.2.2 0 (.inr r) (.inr s) rfl rfl

theorem original_fixed_targets_can_fail_after_real_source_replay442 :
    Fits problem.state (model effect effect) ∧ Fits problem.state (model effect Common.rowEmpty) ∧
    FixedTargets (model effect effect) replayed.event ∧
    ¬FixedTargets (model effect Common.rowEmpty) replayed.event := by
  refine ⟨every_input_and_target_row_fits442 _ _,every_input_and_target_row_fits442 _ _,?_,?_⟩
  · intro i
    have h : i = i0 := Fin.ext (by have ii := i.isLt; change i.val < 1 at ii; change i.val = 0; omega)
    subst i
    exact ⟨refAt effect,rfl,eqv_refl _⟩
  · intro x
    obtain ⟨v,receipt,equiv⟩ := x i0
    change named.receipt.actualEquation (model effect Common.rowEmpty) = some (21,v) at receipt
    rw [actual_replay_has_signed_mixed_value_at_original_target442] at receipt
    have same := (Prod.mk.inj (Option.some.inj receipt)).2
    subst v
    have nope := same_ref_type_requires_same_row442 _ _ equiv
    have present : effect (56,[1,-2]) := rfl
    rw [← nope] at present
    exact present

theorem two_kinds_ref_cannot_satisfy_scalar_target442 (r : Common.Row) (t : Ty) :
    ¬CommonNominalFullCarrier.Subtype (nominal 9 [.inr r,.inl t]) (.base .int) := by
  intro h
  let env : CommonNominalFullDemand.Environment Common.Row :=
    ⟨fun _ => .top,fun _ => []⟩
  have test := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 0)
    0 env (.base .int) (show CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
      (.base .int) (.base .int) from rfl)
  change False at test
  exact test

def fixedScalarAtOwnTarget : Equation := ⟨21,.primitive (.scalar .int) []⟩

def constrainedCore : GeneralDeclarativeI65.State :=
  {core with current := {core.current with ordinary := {core.current.ordinary with
    equations := [intRow,fixedScalarAtOwnTarget]}}}

def scalarOldTarget : I72.Model :=
  {model effect effect with assignment := fun n =>
    (.base .int,(model effect effect).assignment n |>.2)}

theorem old_target_constraint_has_a_model442 : GeneralDeclarativeI65.Fits constrainedCore scalarOldTarget := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro atom member
    change atom ∈ [rowOne,valueTwo] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact Common.rowLe_refl _
    · exact subtype_refl _
  · intro e impossible; cases impossible
  · intro e member
    change e ∈ [intRow,fixedScalarAtOwnTarget] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact eqv_refl _
  · intro view member
    change view ∈ [originalView] at member
    cases List.mem_singleton.mp member
    exact ⟨⟨4,9,[.inr effect,.inl (.base .int)]⟩,rfl,rfl,rfl,rfl⟩
  · intro ori member
    change ori ∈ [inputOrigin,outputObservation] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> rfl

def constrainedPlan : B6MixedRhs401 constrainedCore false (normalize (bodyPattern (.explicit out))) :=
  refPlan 9 6 8 originalUse mode rfl

def constrainedAtlas : B6OccurrenceAtlas401 constrainedCore := ⟨fun q o i body =>
  if q.occurrence == [71,3] && o == 0 && i.val == 0 then
    if h : body = .explicit out then some (h.symm ▸ constrainedPlan) else none
  else none⟩

def constrainedProblem : Problem := ⟨⟨constrainedCore,constrainedAtlas⟩,problem.root⟩

theorem real_preconstrained_target_still_reads_original_source442 :
    (replay442 constrainedProblem wire).isSome = true := by decide +kernel

def constrainedReplay :=
  (replay442 constrainedProblem wire).get real_preconstrained_target_still_reads_original_source442

theorem constrainedMixedCanOnlyBeItsOriginalSymbolicValue442 (m : I72.Model) :
    (constrainedReplay.event.outputs i0).receipt.actualEquation m =
      some (21,nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) := rfl

theorem no_actual_fit_can_retain_loaded_scalar_as_mixed_rhs442 (m : I72.Model)
    (fit : I72.Fits constrainedProblem.state m) :
    ¬FixedTargets m constrainedReplay.event := by
  intro bad
  obtain ⟨rhs,receipt,claimed⟩ := bad i0
  rw [constrainedMixedCanOnlyBeItsOriginalSymbolicValue442] at receipt
  have st := (Prod.mk.inj (Option.some.inj receipt)).2
  subst rhs
  have old := fit.1.1.2 fixedScalarAtOwnTarget (by
    change fixedScalarAtOwnTarget ∈ [intRow,fixedScalarAtOwnTarget]
    simp)
  change Equivalent (m.assignment 21).1 (.base .int) at old
  exact two_kinds_ref_cannot_satisfy_scalar_target442 _ _
    (CommonNominalFullCarrier.subtype_trans claimed.2 old.1)


/-- Dependent package for a literal output of a genuinely replayed event.
Neither the package nor source replay asserts that its equality holds. -/
def stored {p : Problem} (r : Replay p) (i : Fin p.root.demand.outputs.length) :
    RetainedEquation p.state := ⟨p.root,r.event.frame,i,r.event.outputs i⟩

def originalRow := stored replayed i0
def originalFull : FullState := ⟨problem.state,[originalRow]⟩

theorem exact_original_equation444 (m : I72.Model) :
    originalRow.output.receipt.actualEquation m =
      some (21,nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) := rfl

/-- Content depends on the original row/value captures of this SAME model. -/
theorem all_original_full_fits_retain_mixed_target444 (m : I72.Model)
    (fit : FitsFull originalFull m) :
    Equivalent (m.assignment 21).1
      (nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) := by
  obtain ⟨v,receipt,h⟩ := fit.2 originalRow List.mem_cons_self
  rw [exact_original_equation444] at receipt
  have same := (Prod.mk.inj (Option.some.inj receipt)).2
  subst v
  exact h

theorem all_original_full_fits_with_signed_input_retain_that_row444 (m : I72.Model)
    (fit : FitsFull originalFull m) (signed : (m.assignment 1).2 = effect) :
    Equivalent (m.assignment 21).1
      (nominal 9 [.inr effect,.inl (m.assignment 2).1]) := by
  rw [← signed]
  exact all_original_full_fits_retain_mixed_target444 m fit

theorem signed_model_really_fits_original_full444 : FitsFull originalFull (model effect effect) := by
  refine ⟨every_input_and_target_row_fits442 _ _,?_⟩
  intro e member
  cases List.mem_singleton.mp member
  exact ⟨refAt effect,rfl,eqv_refl _⟩

theorem original_old_bad_fit_is_filtered_by_full_retention444 :
    I72.Fits problem.state (model effect Common.rowEmpty) ∧
      ¬FitsFull originalFull (model effect Common.rowEmpty) := by
  refine ⟨every_input_and_target_row_fits442 _ _,?_⟩
  intro h
  have bad := same_ref_type_requires_same_row442 _ _
    (all_original_full_fits_retain_mixed_target444 _ h)
  change Common.rowEmpty = effect at bad
  have present : effect (56,[1,-2]) := rfl
  rw [← bad] at present
  exact present

def otherRequest : Request :=
  {problem.root with demand := {problem.root.demand with outputs := [⟨76,22⟩]}}

def otherProblem : Problem := ⟨problem.state,otherRequest⟩

theorem other_request_really_replays444 : (replay442 otherProblem wire).isSome = true := by
  decide +kernel

def otherReplay := (replay442 otherProblem wire).get other_request_really_replays444
def otherRow := stored otherReplay (⟨0,by decide⟩ : Fin otherRequest.demand.outputs.length)
def otherFull : FullState := ⟨problem.state,[otherRow]⟩

theorem other_row_has_exact_other_address_and_same_source444 (m : I72.Model) :
    otherRow.occurrence = [71,3] ∧
    otherRow.declarationOrdinal = 0 ∧
    otherRow.outputOrdinal.val = 0 ∧
    otherRow.body = .explicit out ∧
    otherRow.kind = CommonDeclaredNominalInspection.Kind.value ∧
    otherRow.target = 22 ∧
    otherRow.output.receipt.actualEquation m =
      some (22,nominal 9 [.inr (m.assignment 1).2,.inl (m.assignment 2).1]) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_fixed_addresses_differ444 : originalRow.target ≠ otherRow.target := by
  change 21 ≠ 22
  decide

/-- Same old state, same original lexical RHS, and a real fitting
model for the other output slot: it proves nothing at original 21. -/
theorem wrong_slot_does_not_substitute444 :
    FitsFull otherFull (model effect Common.rowEmpty effect) ∧
    ¬FitsFull originalFull (model effect Common.rowEmpty effect) := by
  refine ⟨⟨every_input_and_target_row_fits442 _ _ _,?_⟩,?_⟩
  · intro e member
    cases List.mem_singleton.mp member
    exact ⟨refAt effect,rfl,eqv_refl _⟩
  · intro bad
    have eq := same_ref_type_requires_same_row442 _ _
      (all_original_full_fits_retain_mixed_target444 _ bad)
    change Common.rowEmpty = effect at eq
    have present : effect (56,[1,-2]) := rfl
    rw [← eq] at present
    exact present

def loadedFull : FullState := ⟨constrainedProblem.state,[stored constrainedReplay i0]⟩

theorem loaded_old_scalar_still_has_its_original_model444 :
    FitsFull (liftState constrainedProblem.state) scalarOldTarget :=
  (fits_iff_fitsFull_liftState _ _).mp old_target_constraint_has_a_model442

theorem conjunction_with_preexisting_int_has_no_fitting_model444 (m : I72.Model) :
    ¬FitsFull loadedFull m := by
  intro full
  apply no_actual_fit_can_retain_loaded_scalar_as_mixed_rhs442 m full.1
  intro i
  have same : i = i0 := Fin.ext (by have hi := i.isLt; change i.val < 1 at hi; change i.val = 0; omega)
  subst i
  exact full.2 (stored constrainedReplay i0) List.mem_cons_self

#print axioms original_mixed_associated_source_replays442
#print axioms all_original_full_fits_retain_mixed_target444
#print axioms all_original_full_fits_with_signed_input_retain_that_row444
#print axioms signed_model_really_fits_original_full444
#print axioms original_old_bad_fit_is_filtered_by_full_retention444
#print axioms other_request_really_replays444
#print axioms other_row_has_exact_other_address_and_same_source444
#print axioms actual_fixed_addresses_differ444
#print axioms wrong_slot_does_not_substitute444
#print axioms real_preconstrained_target_still_reads_original_source442
#print axioms loaded_old_scalar_still_has_its_original_model444
#print axioms conjunction_with_preexisting_int_has_no_fitting_model444

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442.FullStateExample444
