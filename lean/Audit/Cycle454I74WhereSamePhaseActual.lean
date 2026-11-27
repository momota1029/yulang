import Yulang.GeneralDeclarativeI65I74WhereSamePhaseSource454

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhaseActual454
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

def build (ordinary : GeneralDeclarativeHead320.State) (sourceRoots := roots) : Option FullProblem := do
  let graph ← compile listSource
  let author ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,author⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],sourceRoots,[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨state,atlas⟩,⟨[27,31],⟨7,[point 0,point 5,point 7],[]⟩⟩⟩)

def p : FullProblem := (build raw).get (by decide +kernel)
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



open InternalK2452 SamePhase454
open GroupedEntry453 (GroupedReport OriginView)

def thirdCyclicRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := [edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias,edge 4 4]}

def thirdCyclicRoots : List Origin :=
  [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨7,[44],listPoint410 90 4⟩,
    ⟨4,[45],listPoint410 90 4⟩]

def thirdCyclic : FullProblem :=
  (build thirdCyclicRaw thirdCyclicRoots).get (by decide +kernel)

def thirdModel : I72.Model :=
  ⟨fun _ => (mu,Common.rowEmpty),fun _ => none,fun n =>
      if n = 0 then some (listPoint410 90 1) else if n = 5 then some (listPoint410 90 6)
      else if n = 7 then some (listPoint410 90 4) else if n = 4 then some (listPoint410 90 4) else none⟩

theorem two_same_role_cyclic_classes_have_a_real_common_fit454 :
    FitsFull thirdCyclic.state thirdModel := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    change a ∈ [self 1,self 6,self 4,self 2] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro _ bad; cases bad
  · intro row seen
    change row ∈ [edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias,edge 4 4] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl)
    all_goals first | exact mu_is_one_exact_unfold451 | exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro src real
    change src ∈ thirdCyclicRoots at real
    simp only [thirdCyclicRoots,List.mem_cons,List.not_mem_nil,or_false] at real
    rcases real with rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad

def wThird : RootWire := .cycle ⟨0,⟨5,.same,4⟩,[],.same⟩
def cyclicWire : SourceDiagnosticWire :=
  ⟨parent,⟨⟨[17,17,99],matrix⟩,[w1,w6,wThird]⟩⟩

def a : OriginView := (0,60,[27,31,0],8,1,true)
def b : OriginView := (1,61,[27,31,1],8,6,true)
def c : OriginView := (2,62,[27,31,2],8,4,true)
def correct : GroupedReport := ⟨[27,31],89,[[a,b],[c]]⟩
def checked (p : FullProblem) (r : GroupedReport) (w : SourceDiagnosticWire) : Bool :=
  check_full454 p (.rawGrouped r) (.rawGrouped w)

def wrongPartition : SourceDiagnosticWire :=
  ⟨parent,⟨⟨[17,17,17],matrix⟩,[w1,w6,wThird]⟩⟩

/-- info: [true, true, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [checked thirdCyclic correct cyclicWire,
  checked thirdCyclic {correct with origins := [[c],[a,b]]} cyclicWire,
  checked thirdCyclic {correct with origins := [[a,b,c]]} cyclicWire,
  checked thirdCyclic {correct with origins := [[b,a],[c]]} cyclicWire,
  checked thirdCyclic {correct with origins := [[a,b]]} cyclicWire,
  checked thirdCyclic {correct with origins := [[a,b],[c],[c]]} cyclicWire,
  checked thirdCyclic {correct with parentOccurrence := [27,31,2]} cyclicWire,
  checked thirdCyclic correct wrongPartition,
  checked cycleAtParent correct cyclicWire]

def exactTwoClasses : Prop :=
  RawSame thirdCyclicRaw (8,1) (8,6) ∧ ¬RawSame thirdCyclicRaw (8,1) (8,4) ∧
    ¬RawSame thirdCyclicRaw (8,6) (8,4)

theorem exact_distinct_actual_cyclic_class_links454 : exactTwoClasses := by
  refine ⟨⟨rfl,.backward (by decide +kernel)⟩,?_,?_⟩
  · exact (exact_raw_pair_false450 ..).mp ⟨.separate sep14,by decide +kernel⟩
  · exact (exact_raw_pair_false450 ..).mp ⟨.separate sep14,by decide +kernel⟩

theorem actual_third_child_root_is_cyclic454 :
    RootCycle thirdCyclic.state.base ⟨[27,31,2],⟨8,[point 4],[]⟩⟩ :=
  GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨5,.same,4⟩,[],.same⟩) (by decide +kernel)

#print axioms two_same_role_cyclic_classes_have_a_real_common_fit454
#print axioms exact_distinct_actual_cyclic_class_links454
#print axioms actual_third_child_root_is_cyclic454


/-- The third genuine request remains in the checked original roster,
but at its own safe root there is no authorized list-frame source.
Neither selectedness nor any general pending/rejected verdict is inferred. -/
def safeWithoutLeafRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := [edge 0 1,edge 5 6,edge 7 4,edge 1 1,sourceAlias]}

def safeWithoutLeafRoots : List Origin :=
  [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨7,[44],listPoint410 90 4⟩]

def safeWithoutLeaf : FullProblem :=
  (build safeWithoutLeafRaw safeWithoutLeafRoots).get (by decide +kernel)

def safeThirdRequest : I72.Request := ⟨[27,31,2],⟨8,[point 4],[]⟩⟩

private theorem singleFrameHasOriginalAt {s : GeneralDeclarativeI65.State} {arg : GeneralDeclarativeWhere319.Capture}
    {heads : List GeneralDeclarationPatterns.Pattern}
    (frame : ListSites449.Frame.AuthoredFrame s [arg] heads) :
    ∃ o ∈ s.origins, o.slot = arg.lower := by
  cases frame with
  | cons site _ => exact ⟨site.origin,site.authored,site.lower⟩

theorem actual_safe_third_has_no_G02_leaf_plan454 :
    ∀ t : Tree, ¬ Nonempty (ChildPlan safeWithoutLeaf.state.base safeThirdRequest t) := by
  rintro _ ⟨plan⟩
  cases plan with
  | cycle cy =>
    exact SplitEscape446.checked_split_escape_excludes_exact_raw_K2446
      (s := safeWithoutLeafRaw) (site := 4) (w := e4) (by decide +kernel)
      ((root_cycle_exact_named_point451 (⟨4,rfl⟩ : ActualPoint safeThirdRequest)).mp cy)
  | leaf leaf =>
    have existsAt4 : ∃ o ∈ safeWithoutLeafRoots, o.slot = 4 :=
      singleFrameHasOriginalAt leaf.chosen.roster
    simp [safeWithoutLeafRoots] at existsAt4

def safeOnly : GroupedReport := ⟨[27,31],89,[[a,b]]⟩
def withoutLeafWire : SourceDiagnosticWire :=
  ⟨parent,⟨⟨[17,17,99],matrix⟩,[w1,w6,w4]⟩⟩
def withoutSafeStatus : SourceDiagnosticWire :=
  ⟨parent,⟨⟨[17,17,99],matrix⟩,[w1,w6]⟩⟩

def actualSafeChildPresent : Bool :=
  ((readInternalReport452 safeWithoutLeaf withoutLeafWire).map fun out =>
    (out.original.diagnostics.marks.map markView) ==
    [(0,60,[27,31,0],8,1,17,true),(1,61,[27,31,1],8,6,17,true),(2,62,[27,31,2],8,4,99,false)]).getD false

/-- info: [true, true, false, false] -/
#guard_msgs in
#eval [actualSafeChildPresent,checked safeWithoutLeaf safeOnly withoutLeafWire,
  checked safeWithoutLeaf safeOnly withoutSafeStatus,checked safeWithoutLeaf correct withoutLeafWire]

#print axioms actual_safe_third_has_no_G02_leaf_plan454


def allSafeRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := [edge 0 1,edge 5 6,edge 7 4,sourceAlias]}

def allSafe : FullProblem :=
  (build allSafeRaw safeWithoutLeafRoots).get (by decide +kernel)

def e16 := cut [2,0,2,2,2,2,0,2]
def safeMatrix : List (List ExactPairWire) :=
  [[.linked .same,.linked (.backward 3),.separate sep14],
   [.linked (.forward 3),.linked .same,.separate sep14],
   [.separate sep14,.separate sep14,.linked .same]]
def allSafeWire : SourceDiagnosticWire :=
  ⟨parent,⟨⟨[17,17,99],safeMatrix⟩,[.safe e16,.safe e16,w4]⟩⟩

/-- info: [true, false, false] -/
#guard_msgs in
#eval [((readInternalReport452 allSafe allSafeWire).map fun x => x.groups.isEmpty).getD false,
  checked allSafe {safeOnly with origins := []} allSafeWire,checked allSafe safeOnly allSafeWire]

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhaseActual454
