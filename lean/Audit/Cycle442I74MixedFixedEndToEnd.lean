import Yulang.GeneralDeclarativeI65I74MixedFixedRead442

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example
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

def model (inputEffect targetEffect : Common.Row) : I72.Model where
  assignment := fun n =>
    (if n = 21 then refAt targetEffect else .base .int,
     if n = 1 then inputEffect else Common.rowEmpty)
  authoredValues := fun n =>
    if n = 21 then some ⟨4,9,[.inr inputEffect,.inl (.base .int)]⟩ else none
  nativeSyntax := fun n => if n = 0 ∨ n = 21 then some (endpoint 9 1 2) else none

theorem every_input_and_target_row_fits442 (inputEffect targetEffect : Common.Row) :
    I72.Fits problem.state (model inputEffect targetEffect) := by
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

#print axioms original_mixed_associated_source_replays442
#print axioms replayed_exact_original_fields442
#print axioms every_input_and_target_row_fits442
#print axioms actual_replay_has_signed_mixed_value_at_original_target442
#print axioms same_ref_type_requires_same_row442
#print axioms original_fixed_targets_can_fail_after_real_source_replay442
end Yulang.GeneralDeclarativeI65.I72.MixedFixed442.Example
