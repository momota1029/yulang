import Yulang.GeneralDeclarativeMergeCenters324
import Yulang.GeneralDeclarativeI65I74WhereGroupedEntry453
import Yulang.GeneralDeclarativeI65I74WhereLiteralInternal452

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedScopeBoundary453
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open PresenceNormalForm (Atom)
open Checker408 (Result)
open CommonRoleOutermostResolver (Tree)

def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩

def whereFirst : Clause := ⟨60,8,[.var 11],[]⟩
def whereSecond : Clause := ⟨61,8,[.var 12],[]⟩
def whereThird : Clause := ⟨62,8,[.var 13],[]⟩

def authoredParent : Declaration :=
  ⟨89,7,[.app 90 [.var 11],.app 90 [.var 12],.app 90 [.var 13]],
    [whereFirst,whereSecond,whereThird],[],[]⟩

def safeImpl : Declaration := ⟨88,8,[.app 90 [.var 14]],[],[],[]⟩

def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,3,[]⟩,⟨8,1,[]⟩]⟩,[authoredParent,safeImpl]⟩

def edge (owner child : Nat) : Equation := ⟨owner,.nominal 90 [.variable child]⟩
def sourceAlias : Equation := ⟨6,.variable 1⟩
def self (p : Nat) : Atom Nat := .tyLe (.var p) (.var p)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[self 1,self 6,self 4,self 2],[]⟩,[edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias,edge 4 2]⟩

def roots : List Origin :=
  [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨7,[44],listPoint410 90 4⟩,⟨4,[45],listPoint410 90 2⟩]

def build (ordinary : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile listSource
  let author ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,author⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],roots,[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨state,atlas⟩,⟨[27,31],⟨7,[point 0,point 5,point 7],[]⟩⟩⟩)

def p : FullProblem := (build raw).get (by decide +kernel)
def noAlias : FullProblem := (build {raw with equations := [edge 0 1,edge 5 6,edge 7 4,edge 1 1]}).get (by decide +kernel)
def cycleAtParent : FullProblem := (build {raw with equations := edge 0 0 :: raw.equations}).get (by decide +kernel)

def cut (xs : List Nat) : ExactEscapeWire := ⟨List.range 8,xs⟩
def e0 := cut [0,1,2,2,2,2,1,2]
def e5 := cut [2,1,2,2,2,0,1,2]
def e7 := cut [2,2,1,2,1,2,2,0]
def e4 := cut [2,2,1,2,0,2,2,2]
def sep14 := cut [2,0,2,2,1,2,0,2]
def parent : ParentWire := ⟨[0,1,2],[e0,e5,e7]⟩
def w1 : RootWire := .cycle ⟨0,⟨3,.same,1⟩,[],.same⟩
def w6 : RootWire := .cycle ⟨0,⟨3,.forward 4,1⟩,[],.backward 4⟩
def w4 : RootWire := .safe e4
def statusWires : List RootWire := [w1,w6,w4]

def matrix : List (List ExactPairWire) :=
  [[.linked .same,.linked (.backward 4),.separate sep14],
   [.linked (.forward 4),.linked .same,.separate sep14],
   [.separate sep14,.separate sep14,.linked .same]]

def actualWire : SourceDiagnosticWire := ⟨parent,⟨⟨[17,17,99],matrix⟩,statusWires⟩⟩
def markView (m : OriginalMark) : Nat × Nat × List Nat × Nat × Nat × Nat × Bool :=
  (m.ordinal,m.writtenId,m.request.occurrence,m.request.demand.role,m.actualCenter,m.classLabel,m.rawK2)

def emitted (p : FullProblem) (w : SourceDiagnosticWire) :=
  (readOriginalWhereProfiles451 p w).map fun a => a.diagnostics.marks.map markView

def emitsExpected (x : FullProblem) (w : SourceDiagnosticWire) : Bool :=
  (emitted x w).isSome

def muState : CommonNominalSyntax.State Common.Row := .block [.nominal 90 [.inl (.inl 0)]] 0
def mu : Ty := .nominal 90 [.inl muState]
def scalar : Ty := .base .bool

theorem mu_is_one_exact_unfold451 : Equivalent mu (nominal 90 [.inl mu]) := by
  have same (depth : Nat) : CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (nominal 90 [.inl mu]) := by
    cases depth <;> rfl
  constructor
  · intro depth
    rw [←same depth]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro depth
    rw [same depth]
    exact CommonNominalFullDemand.producerLe_refl _

def model : I72.Model :=
  ⟨fun n => ((if n = 2 then scalar else if n = 4 then nominal 90 [.inl scalar] else if n = 7 then nominal 90 [.inl (nominal 90 [.inl scalar])] else mu),Common.rowEmpty),
    fun _ => none,fun n =>
      if n = 0 then some (listPoint410 90 1) else if n = 5 then some (listPoint410 90 6)
      else if n = 7 then some (listPoint410 90 4) else if n = 4 then some (listPoint410 90 2) else none⟩

theorem actual_original_same_role_cohort_state_fits451 : FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    change a ∈ [self 1,self 6,self 4,self 2] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro _ bad; cases bad
  · intro row seen
    change row ∈ [edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias,edge 4 2] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact mu_is_one_exact_unfold451
    · exact mu_is_one_exact_unfold451
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact mu_is_one_exact_unfold451
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro src real
    change src ∈ roots at real
    simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at real
    rcases real with rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

theorem same_role_actual_centers_are_exactly_two_raw_classes451 :
    RawSame raw (8,1) (8,6) ∧ ¬RawSame raw (8,1) (8,4) ∧
      ¬RawSame raw (8,6) (8,4) := by
  refine ⟨⟨rfl,.backward (by decide +kernel)⟩,?_,?_⟩
  · exact (exact_raw_pair_false450 ..).mp ⟨.separate sep14,by decide +kernel⟩
  · exact (exact_raw_pair_false450 ..).mp ⟨.separate sep14,by decide +kernel⟩

theorem both_original_request_roots_actually_cyclic_and_third_is_safe451 :
    RootCycle p.state.base ⟨[27,31,0],⟨8,[point 1],[]⟩⟩ ∧
      RootCycle p.state.base ⟨[27,31,1],⟨8,[point 6],[]⟩⟩ ∧
      ¬RootCycle p.state.base ⟨[27,31,2],⟨8,[point 4],[]⟩⟩ := by
  refine ⟨GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨3,.same,1⟩,[],.same⟩) (by decide +kernel),
    GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨3,.forward 4,1⟩,[],.backward 4⟩) (by decide +kernel),?_⟩
  exact fun cy => SplitEscape446.checked_split_escape_excludes_exact_raw_K2446
    (s := raw) (site := 4) (w := e4) (by decide +kernel) ((root_cycle_exact_named_point451 ⟨4,rfl⟩).mp cy)


open InternalK2452
open OutputPhase452
open LiteralAndInternal452

def genuineExtra : List AdditionalChoice := [.useRawStatus,.useRawStatus,.leaf ⟨[3],[e4]⟩]
def expected : Result := ⟨.selected 89 [.rejected,.rejected,.selected 88 []],.rejected,[]⟩
def readBoth (extra : List AdditionalChoice) : Bool :=
  ((readScopedLiteralReport p ⟨actualWire,extra⟩).map fun got =>
    Check408.matchesNoWrites got.localK2.report expected.tree expected.verdict &&
    decide (got.actual.diagnostics.cohortsWithOrigins.map (fun g => g.marks.map OriginalMark.writtenId) =
      [[60,61],[62]]) &&
    (got.internal.groups.map (fun g => g.marks.map OriginalMark.literal) ==
      [[(0,60,[27,31,0],8,1,true),(1,61,[27,31,1],8,6,true)]])).getD false

/-- info: [true, false, false, false, false] -/
#guard_msgs in
#eval [readBoth genuineExtra,readBoth [.useRawStatus,.useRawStatus,.useRawStatus],
  readBoth [.leaf ⟨[3],[e4]⟩,.useRawStatus,.useRawStatus],
  readBoth [.useRawStatus,.useRawStatus,.leaf ⟨[2],[e4]⟩],
  NoSiblingMerge.check_full450 p expected (.whereRoot ⟨parent,[
    .raw ⟨0,⟨3,.same,1⟩,[],.same⟩,.raw ⟨0,⟨3,.forward 4,1⟩,[],.backward 4⟩,.leaf ⟨[3],[e4]⟩]⟩)]

theorem parsed_source_has_exact_phase_output_and_identical_same_model452
    {w : ScopedLiteralInput} {r : ScopedLiteralReport p}
    (read : readScopedLiteralReport p w = some r)
    (xs : List (ActualPair (p := p) r.actual.diagnostics)) :
    emissionRows xs = [] ∧
    GeneralDeclarativeCaptureClosure320.withOrdinary p.state.base.core.current.ordinary
      (emissionRows xs) = p.state.base.core.current.ordinary ∧
    readInternalReport452 p w.original = some r.internal ∧
    WhereSites450.ReportEvidence p.state.base model p.root r.localK2.report := by
  have same := output_equation_substep_exactly_preserves_raw_input452 xs
  exact ⟨same.1,same.2, read_both_retains_the_same_checked_profile_and_internal_groups452 read,
    (any_literal_replay_preserves_original_scoped_report_meaning452 p r).2 model
      actual_original_same_role_cohort_state_fits451⟩

#print axioms actual_original_same_role_cohort_state_fits451
#print axioms same_role_actual_centers_are_exactly_two_raw_classes451
#print axioms both_original_request_roots_actually_cyclic_and_third_is_safe451
#print axioms parsed_source_has_exact_phase_output_and_identical_same_model452
end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedScopeBoundary453

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedScopeBoundary453
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarativeWitnessDeclaredState357 (point)
open CommonNominalFullCarrier (Ty Equivalent nominal)

def duplicateAuthoredRhs : GeneralDeclarativeHead320.State :=
  {raw with equations := [edge 0 1,edge 5 6,edge 7 4,edge 1 1,edge 6 1,edge 4 2]}
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)

def extendedRoots : List Origin := roots ++ [⟨6,[46],listPoint410 90 1⟩]

def buildStructuralPair : Option FullProblem := do
  let graph ← compile listSource
  let author ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,author⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,duplicateAuthoredRhs,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],extendedRoots,[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨state,atlas⟩,⟨[27,31],⟨7,[point 0,point 5,point 7],[]⟩⟩⟩)
def structuralPair : FullProblem := buildStructuralPair.get (by decide +kernel)

def extendedModel : I72.Model :=
  ⟨model.assignment,fun _ => none,fun n =>
      if n = 0 then some (listPoint410 90 1) else if n = 5 then some (listPoint410 90 6)
      else if n = 7 then some (listPoint410 90 4) else if n = 4 then some (listPoint410 90 2)
      else if n = 6 then some (listPoint410 90 1) else none⟩
def e6Independent := cut [2,1,2,2,2,2,0,2]
def allSeparate := cut (List.range 8)

theorem structurally_equal_centers_without_raw_alias453 :
    (∀ m, FitsFull structuralPair.state m → Equivalent (m.assignment 1).1 (m.assignment 6).1) ∧
    ¬ RawSame duplicateAuthoredRhs (8,1) (8,6) := by
  refine ⟨?_,(exact_raw_pair_false450 ..).mp ⟨.separate allSeparate,by decide +kernel⟩⟩
  intro m fit
  have valid : GeneralDeclarativeHead320.Models duplicateAuthoredRhs m.assignment := fit.1.1.1
  have l := valid.2 (edge 1 1) (by decide +kernel)
  have r := valid.2 (edge 6 1) (by decide +kernel)
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans l ⟨r.2,r.1⟩

theorem structural_pair_root_status_differs453 :
    RootCycle structuralPair.state.base ⟨[27,31,0],⟨8,[point 1],[]⟩⟩ ∧
    ¬ RootCycle structuralPair.state.base ⟨[27,31,1],⟨8,[point 6],[]⟩⟩ := by
  refine ⟨GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨3,.same,1⟩,[],.same⟩)
    (by decide +kernel),?_⟩
  exact fun cy => SplitEscape446.checked_split_escape_excludes_exact_raw_K2446
    (s := duplicateAuthoredRhs) (site := 6) (w := e6Independent) (by decide +kernel)
    ((root_cycle_exact_named_point451 ⟨6,rfl⟩).mp cy)

theorem structural_pair_has_actual_model453 : FitsFull structuralPair.state extendedModel := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    change a ∈ [self 1,self 6,self 4,self 2] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro _ bad; cases bad
  · intro row seen
    change row ∈ [edge 0 1,edge 5 6,edge 7 4,edge 1 1,edge 6 1,edge 4 2] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact mu_is_one_exact_unfold451
    · exact mu_is_one_exact_unfold451
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact mu_is_one_exact_unfold451
    · exact mu_is_one_exact_unfold451
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro src real
    change src ∈ extendedRoots at real
    simp only [extendedRoots,roots,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at real
    rcases real with rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

open LiteralAndInternal452 InternalK2452 OutputPhase452
def differentRawMatrix : List (List ExactPairWire) :=
  [[.linked .same,.separate allSeparate,.separate allSeparate],
   [.separate allSeparate,.linked .same,.separate allSeparate],
   [.separate allSeparate,.separate allSeparate,.linked .same]]

def structuralInput : ScopedLiteralInput :=
  ⟨⟨parent,⟨⟨[17,18,99],differentRawMatrix⟩,[w1,.safe e6Independent,w4]⟩⟩,
    [.useRawStatus,.leaf ⟨[4],[e6Independent]⟩,.leaf ⟨[3],[e4]⟩]⟩

def structuralReportClasses : List (List Nat) :=
  ((readInternalReport452 structuralPair structuralInput.original).map fun r =>
    r.groups.map (fun g => g.marks.map OriginalMark.writtenId)).getD []

/-- Real source and exact raw only: the source-only replay isolates clause 60 from raw-safe clause 61.
It does not claim that authored constructor-equation equivalence preserves K2. -/
theorem structural_pair_replays_originals_with_raw_only_singleton453 :
    structuralReportClasses = [[60]] := by decide +kernel

open GeneralNominalDemandMerging (SameInputs SameOrigin)

theorem structural_origin_equality_is_actual_sameInputs453
    (r : ScopedLiteralReport structuralPair)
    (x : SourcePointAt r.actual.parent 0) (y : SourcePointAt r.actual.parent 1)
    (rx : x.original.role = 8) (ry : y.original.role = 8)
    (cx : x.capture = 1) (cy : y.capture = 6) :
    SameInputs (allAssignments structuralPair.state) x.site y.site := by
  have identical : SameOrigin (allAssignments structuralPair.state) (.source x.capture) (.source y.capture) := by
    intro a seen
    obtain ⟨m,fit,rfl⟩ := seen
    refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
    intro _ _ ra rb
    cases ra
    cases rb
    rw [cx,cy]
    exact structurally_equal_centers_without_raw_alias453.1 m fit
  exact ⟨rx.trans ry.symm,.cons ⟨_,_,rfl,rfl,identical⟩ .nil⟩

#print axioms structural_pair_replays_originals_with_raw_only_singleton453
#print axioms structural_origin_equality_is_actual_sameInputs453
open GroupedEntry453 (check_full453)

def rawOnlyCumulativeReport : GroupedEntry453.GroupedReport :=
  ⟨[27,31],89,[[(0,60,[27,31,0],8,1,true)]]⟩

def allegedSemanticCohortReport : GroupedEntry453.GroupedReport :=
  ⟨[27,31],89,[[(0,60,[27,31,0],8,1,true),(1,61,[27,31,1],8,6,true)]]⟩

theorem guarded_fails_nonsaturated_actual_roster453 :
    check_full453 structuralPair (.grouped rawOnlyCumulativeReport) (.grouped structuralInput) = false ∧
    check_full453 structuralPair (.grouped allegedSemanticCohortReport) (.grouped structuralInput) = false := by
  decide +kernel

#print axioms guarded_fails_nonsaturated_actual_roster453
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models)
open GeneralDeclarativeMergeCenters324 (centerPair)
open GeneralDeclarativeBounds319 (Bound)

def testAlignedRaw : GeneralDeclarativeHead320.State :=
  withOrdinary duplicateAuthoredRhs (centerPair 1 6)

theorem exact_ordinary_models_unchanged_after_center_pair453 (m : GeneralNominalCommonBridge.Assignment) :
    GeneralDeclarativeHead320.Models testAlignedRaw m ↔ GeneralDeclarativeHead320.Models duplicateAuthoredRhs m := by
  unfold testAlignedRaw
  rw [ordinary_models]
  refine ⟨And.left,fun valid => ⟨valid,?_⟩⟩
  have l := valid.2 (edge 1 1) (by decide +kernel)
  have r := valid.2 (edge 6 1) (by decide +kernel)
  have eq := GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans l ⟨r.2,r.1⟩
  intro row found
  change row ∈ [.tyLe (.var 6) (.var 1),.tyLe (.var 1) (.var 6)] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl
  · exact eq.2
  · exact eq.1

theorem aligned_K2_at_previous_safe_original453 :
    GeneralDeclarativePriority321.RootRecurs testAlignedRaw ⟨8,[point 6],[]⟩ := by
  have one : GeneralDeclarativePriority321.RootRecurs testAlignedRaw ⟨8,[point 1],[]⟩ :=
    GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨3,.same,1⟩,[],.same⟩) (by decide +kernel)
  have link : GeneralDeclarativeLowerKnown321.Alias testAlignedRaw 1 6 :=
    .bounds (.constraint (by decide +kernel)) (.constraint (by decide +kernel))
  obtain ⟨c,listed,cy⟩ := one
  have root : c = point 1 := List.mem_singleton.mp listed
  subst c
  refine ⟨point 6,by simp,?_⟩
  exact (GeneralDeclarativeK2Alias321.alias_cycle_iff link).mp cy

#print axioms exact_ordinary_models_unchanged_after_center_pair453
#print axioms aligned_K2_at_previous_safe_original453
#print axioms structurally_equal_centers_without_raw_alias453
#print axioms structural_pair_root_status_differs453
#print axioms structural_pair_has_actual_model453

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedScopeBoundary453
