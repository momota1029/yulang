import Yulang.GeneralDeclarativeI65I74SelectedEntry447
import Yulang.GeneralDeclarativeI65I74MixedFixedRead442

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442.SelectedHeaderBoundary447
open GeneralDeclarativeI65
open RetainedFull445 RetainedSplit446
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration DeclarationChecked Clause Checked)
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

open GeneralDeclarationPatterns (Pattern StableSmaller checkSmaller_exact)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage DeclarationCovered)
open GeneralDeclarativeWitnessSignature349 (checked_signature)
open GeneralDeclarativeWitnessChecks349 (identified produced output_only scope_sound)

def intPattern : Pattern := .app 20 []
def concreteTick : Pattern := .variant 88 intPattern
def groundClause : Clause := ⟨600,9,[intPattern],[]⟩
def groundDecl : Declaration := ⟨82,8,[concreteTick],[groundClause],[],[]⟩

def enlargedCatalogue : InputBundle :=
  {catalogue [groundDecl,declaration] with roles :=
    ⟨0,[⟨7,1,[(76,none)]⟩,⟨8,1,[]⟩,⟨9,1,[]⟩]⟩}

def makeEnlargedEnv : Option Environment := do
  let graph ← compile projectedRun
  let book ← GeneralSourceMetadataBareBundle291.compile enlargedCatalogue
  pure ⟨3,1,1,projectedRun,graph,book⟩

def enlargedEnv := makeEnlargedEnv.get (by decide +kernel)
def enlargedCore := core enlargedEnv

theorem enlarged_roles_are_valid446 :
    GeneralSourceMetadataRoles291.Valid enlargedEnv.source.roles :=
  (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)

theorem enlarged_mode_coverage446 : Coverage enlargedEnv :=
  (GeneralDeclarativeWitnessModeCoverage357.check_exact enlarged_roles_are_valid446).mp (by decide +kernel)

private theorem originalCovered : DeclarationCovered enlargedEnv declaration :=
  enlarged_mode_coverage446.1 declaration (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem groundCovered : DeclarationCovered enlargedEnv groundDecl :=
  enlarged_mode_coverage446.1 groundDecl List.mem_cons_self

theorem unrelated_ground_clause_is_stable446 :
    StableSmaller groundDecl.head groundClause.arguments := by
  intro c
  change GeneralDeclarationPatterns.Smaller groundDecl.head groundClause.arguments
  exact (checkSmaller_exact _ _).mp (by decide +kernel)

theorem independent_unrelated_ground_is_checked446 :
    DeclarationChecked (authoredRegistry enlargedCore.current).constructors
      (authoredRegistry enlargedCore.current).roles groundDecl := by
  refine ⟨checked_signature (by decide +kernel),identified (by decide +kernel),
    produced (by decide +kernel),output_only (by decide +kernel),scope_sound (by decide +kernel),
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl groundCovered,?_,?_,?_,?_⟩
  · intro c present
    change c ∈ [groundClause] at present
    cases List.mem_singleton.mp present
    exact GeneralDeclarativeWitnessProblem349.splitAnd
      (show GeneralDeclarativeWitnessChecks349.counts groundDecl.head groundClause.arguments = true
       from by decide +kernel)
  · intro c present
    change c ∈ [groundClause] at present
    cases List.mem_singleton.mp present
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c present
    change c ∈ [groundClause] at present
    cases List.mem_singleton.mp present
    unfold GeneralDeclarationPatterns.ConservativeSmaller
    decide +kernel
  · intro c present
    change c ∈ [groundClause] at present
    cases List.mem_singleton.mp present
    exact unrelated_ground_clause_is_stable446

theorem independent_enlarged_registry_is_checked446 : Checked (authoredRegistry enlargedCore.current) := by
  constructor
  · change [82,81].Nodup
    decide
  · intro d used
    change d ∈ [groundDecl,declaration] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with same|same
    · subst d
      exact independent_unrelated_ground_is_checked446
    · subst d
      exact MergedOutput439.checks_declaration_sound439 originalCovered (by decide +kernel)

theorem conservative_full_header_misses_the_ground_scope446 :
    MergedOutput439.checkHeader439 enlargedEnv = false := by decide +kernel

theorem enlarged_header_is_not_ready446 : ¬HeaderReady445 enlargedEnv := by
  intro h
  have check := ready_header_check445 h
  rw [conservative_full_header_misses_the_ground_scope446] at check
  cases check

#print axioms unrelated_ground_clause_is_stable446
#print axioms independent_unrelated_ground_is_checked446
#print axioms independent_enlarged_registry_is_checked446
#print axioms conservative_full_header_misses_the_ground_scope446
#print axioms enlarged_header_is_not_ready446

def wideUse : Use enlargedCore.current.environment 9 2 :=
  (readUse enlargedCore.current.environment 9 2).get (by decide +kernel)

theorem wideMode : names wideUse.mode 2 = some layout := by decide +kernel
def widePlan : B6MixedRhs401 enlargedCore false (normalize (bodyPattern (.explicit out))) :=
  refPlan 9 6 8 wideUse wideMode rfl

def wideAtlas : B6OccurrenceAtlas401 enlargedCore := ⟨fun q o i body =>
  if q.occurrence == [71,3] && o == 1 && i.val == 0 then
    if h : body = .explicit out then some (h.symm ▸ widePlan) else none
  else none⟩

def wideProblem : Problem := ⟨⟨enlargedCore,wideAtlas⟩,problem.root⟩

theorem actual_enlarged_candidate_scope_is_original446 :
    visible enlargedCore wideProblem.root = [declaration] := rfl

theorem enlarged_original_site_raw_safe446 :
    ¬RootCycle (inputOnly wideProblem).state (inputOnly wideProblem).root := by
  rintro ⟨arg,member,cycle⟩
  change arg ∈ [point 0] at member
  cases List.mem_singleton.mp member
  exact Yulang.GeneralDeclarativeI65.I72.SplitEscape446.checked_split_escape_excludes_exact_raw_K2446
    (show Yulang.GeneralDeclarativeI65.I72.SplitEscape446.splitCheck446
        enlargedCore.current.ordinary 0 wire.escape = true from by decide +kernel) cycle

/-- Build the original selected source independently of the global
header checker, which has already been shown false. -/
def actualEnlargedInput : RefPositions441.Original (inputOnly wideProblem).state
    (inputOnly wideProblem).root declaration where
  only := (inputOnly_visible wideProblem).trans actual_enlarged_candidate_scope_is_original446
  checked := independent_enlarged_registry_is_checked446.2 declaration (List.mem_cons_of_mem _ List.mem_cons_self)
  covered := originalCovered
  noWhere := rfl
  noOutputs := rfl
  arg := point 0
  asked := rfl
  key := 9
  rowBinder := 6
  valueBinder := 8
  separateBinders := by decide
  written := rfl
  original := inputOrigin
  authored := List.mem_cons_self
  issuer := rfl
  lower := rfl
  center := rfl
  upper := rfl
  rowName := 1
  valueName := 2
  read := rfl
  use := wideUse
  fromBody := rfl
  table := rfl
  rowAtom := List.mem_cons_self
  valueAtom := List.mem_cons_of_mem _ List.mem_cons_self
  safe := enlarged_original_site_raw_safe446

def actualFrame : AuthoredBodyFrame393 enlargedCore wideProblem.root :=
  frameAtSource395 (originalCandidate actualEnlargedInput).inScope 1 rfl unusedPlacement403
    actualEnlargedInput.capture

def i0 : Fin wideProblem.root.demand.outputs.length := ⟨0,by decide⟩

def actualMixedOutput : OriginalOutput (s := wideProblem.state) actualFrame i0 where
  key := 9
  rowBinder := 6
  valueBinder := 8
  independent := by decide
  use := wideUse
  mode := wideMode
  table := rfl
  bodyId := 100
  supplied := .explicit out List.mem_cons_self rfl
  original := rfl
  rowCap := point 1
  valueCap := point 2
  row := rfl
  value := rfl

def actualEvent : Event wideProblem.state wideProblem.root :=
  ⟨actualFrame,restoreOriginalHead actualEnlargedInput,fun i =>
    (show i0 = i from Fin.ext (by
      have hi := i.isLt
      change i.val < 1 at hi
      change 0 = i.val
      omega)) ▸ actualMixedOutput.named⟩

def actualReplay : Replay wideProblem :=
  ⟨declaration,actualEnlargedInput,actualEvent,rfl,rfl,rfl,rfl,rfl⟩

def actualChoice : SourceSelection wideProblem :=
  ⟨actualReplay,rfl,⟨100,⟨actualMixedOutput,rfl,rfl,rfl,rfl⟩⟩⟩

theorem actual_enlarged_target_is_fresh446 : FreshOutput actualChoice := by
  constructor
  · change 21 ∉ oldReadNames enlargedCore
    decide +kernel
  · change (2 : Nat) ≠ 21
    decide

def full : FullProblem :=
  ⟨retainSelected (liftState wideProblem.state) actualChoice,wideProblem.root⟩

def actualLocal : LocalSelection full.state full.root :=
  selectedIntoEmptyBecomesLocal445 actualChoice actual_enlarged_target_is_fresh446

theorem actual_local_selection_with_inactive_ground_clause_exists446 :
    Nonempty (LocalSelection full.state full.root) ∧
      ¬HeaderReady445 full.state.base.core.current.environment :=
  ⟨⟨actualLocal⟩,enlarged_header_is_not_ready446⟩

theorem actual_enlarged_signed_base_fits446 :
    I72.Fits wideProblem.state (model effect effect) :=
  every_input_and_target_row_fits442 _ _

theorem actual_enlarged_local_has_fitting_model446 : ∃ m : I72.Model, FitsFull full.state m :=
  actualLocal.has_fit_of_old_fit _ actual_enlarged_signed_base_fits446

#print axioms actual_enlarged_candidate_scope_is_original446
#print axioms enlarged_original_site_raw_safe446
#print axioms actual_enlarged_target_is_fresh446
#print axioms actual_local_selection_with_inactive_ground_clause_exists446
#print axioms actual_enlarged_signed_base_fits446
#print axioms actual_enlarged_local_has_fitting_model446

theorem actual_new_entry_cannot_read_the_failed_full_header446 (p : FullProblem)
    (r : Checker408.Result) (w : RefPositions441.Wire)
    (bad : MergedOutput439.checkHeader439 p.state.base.core.current.environment = false) :
    check_full446 p r (.splitOutput w) = false := by
  have notTrue : ¬(MergedOutput439.checkHeader439 p.state.base.core.current.environment = true) := by
    simp [bad]
  have unsupported : replaySelected446 p.old w = none := by
    unfold replaySelected446
    split
    · rename_i d scope
      have missing : replayInput446 (inputOnly p.old) d
          (inputOnly_visible p.old ▸ scope) w = none := by
        unfold replayInput446
        exact dite_eq_right notTrue
      rw [missing]
      rfl
    · rfl
  have noSource : readSource446 p.old w = none := by
    unfold readSource446
    split
    · rfl
    · rename_i _ hit
      rw [unsupported] at hit
      cases hit
  simp [check_full446,noSource]

/-- Actual same independently selected report, valid source registry
and a fitting state. The remaining failure is the inherited full
header checker on a genuinely stable unrelated declaration. -/
theorem checked_registry_selected_report_has_no_split_witness446 :
    Checked (authoredRegistry full.state.base.core.current) ∧
    (∃ m, FitsFull full.state m) ∧
    ClassifiedAsFull full.state full.root actualLocal.report ∧
    (∀ w : RefPositions441.Wire, check_full446 full actualLocal.report (.splitOutput w) = false) :=
  ⟨independent_enlarged_registry_is_checked446,actual_enlarged_local_has_fitting_model446,
    .inr ⟨actualLocal,rfl⟩,fun w => actual_new_entry_cannot_read_the_failed_full_header446 _ _ w
      conservative_full_header_misses_the_ground_scope446⟩

#print axioms actual_new_entry_cannot_read_the_failed_full_header446
#print axioms checked_registry_selected_report_has_no_split_witness446

theorem actual_unfiltered_declaration_ordinal_is_one447 : actualChoice.origin.event.frame.ordinal = 1 := rfl

#print axioms actual_unfiltered_declaration_ordinal_is_one447

def headerSelectedComparison447 : Option (List Bool) := do
  let replay ← RetainedSplit446.SelectedReplay447.readLocalSource full.old wire
  if replay.origin.event.frame.ordinal == 1 && replay.origin.decl.id == 81 then
    some [RetainedSplit446.SelectedReplay447.check_full447 full actualLocal.report (.previous (.splitOutput wire)),
      RetainedSplit446.SelectedReplay447.check_full447 full actualLocal.report (.localSplitOutput wire)]
  else none

/-- info: some [false, true] -/
#guard_msgs in
#eval headerSelectedComparison447

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442.SelectedHeaderBoundary447

