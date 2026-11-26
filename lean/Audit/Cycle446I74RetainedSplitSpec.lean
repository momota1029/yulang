import Yulang.GeneralDeclarativeI65I74MixedFixedRead442
import Yulang.GeneralDeclarativeI65I74RetainedSplitEntry446

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442.SplitEntryExample446
open GeneralDeclarativeI65
open RetainedFull445 RetainedSplit446
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

theorem two_kinds_ref_cannot_satisfy_scalar_target442 (key : Nat) (r : Common.Row) (t : Ty) :
    ¬CommonNominalFullCarrier.Subtype (nominal key [.inr r,.inl t]) (.base .int) := by
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

def comparisonRoot : I72.Request :=
  {problem.root with demand := {problem.root.demand with outputs := [⟨76,22⟩]}}
def otherProblem : Problem := ⟨problem.state,comparisonRoot⟩

/-- All controls go through the same actual data-only entry. No model
or test flag is passed in the witness. If any source replay fails the
executable control returns none, not the requested false result. -/
def actualSplitChecks : Option (List Bool) := do
  let source ← readSource446 problem wire
  let other ← readSource446 otherProblem wire
  let loaded ← readSource446 constrainedProblem wire
  let full : FullProblem := ⟨retainSelected (liftState problem.state) source,problem.root⟩
  let wrong : FullProblem := ⟨retainSelected (liftState problem.state) other,problem.root⟩
  let oldInt : FullProblem := ⟨retainSelected (liftState constrainedProblem.state) loaded,
    constrainedProblem.root⟩
  let oldReport := sourceReport loaded
  let report := sourceReport source
  let w : Witness446 := .splitOutput wire
  let noStore := liftProblem problem
  if full.state.retained.map (·.target) == [21] &&
      wrong.state.retained.map (·.target) == [22] &&
      oldInt.state.retained.map (·.target) == [21] && noStore.state.retained.isEmpty &&
      source.origin.decl.id == 81 && other.origin.decl.id == 81 && loaded.origin.decl.id == 81 then
    some [check_full446 full report w, check_full446 wrong report w,
      check_full446 oldInt oldReport w,check_full446 noStore report w]
  else none

/-- info: some [true, false, false, false] -/
#guard_msgs in
#eval actualSplitChecks

theorem literal_old_Int_fixture_has_model445 : I72.Fits constrainedProblem.state scalarOldTarget :=
  old_target_constraint_has_a_model442

theorem literal_preoutput_signed_fixture_has_old_model445 :
    I72.Fits problem.state (model effect effect) :=
  every_input_and_target_row_fits442 _ _

/-- Even when the original input has been selected, adding the new
retention to the genuine loaded old state cannot overwrite Int. -/
theorem selected_mixed_equation_does_not_overwrite_old_int445
    (source : SourceSelection constrainedProblem) (m : I72.Model) :
    ¬FitsFull (retainSelected (liftState constrainedProblem.state) source) m := by
  intro fit
  have both := (fitsFull_retainSelected_iff445 (liftState constrainedProblem.state) source m).mp fit
  have taken := (original_replayed_ref_is_the_fixed_target_slice442
    source.origin source.own.2.out m).mp both.2
  have old := both.1.1.1.1.2 fixedScalarAtOwnTarget (by
    change fixedScalarAtOwnTarget ∈ [intRow,fixedScalarAtOwnTarget]
    simp)
  change Equivalent (m.assignment 21).1 (.base .int) at old
  change Equivalent (m.assignment 21).1 _ at taken
  exact two_kinds_ref_cannot_satisfy_scalar_target442 _ _ _
    (CommonNominalFullCarrier.subtype_trans taken.2 old.1)

#print axioms literal_old_Int_fixture_has_model445
#print axioms literal_preoutput_signed_fixture_has_old_model445
#print axioms selected_mixed_equation_does_not_overwrite_old_int445

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442.SplitEntryExample446
