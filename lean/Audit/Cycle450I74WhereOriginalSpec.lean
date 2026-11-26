import Yulang.GeneralDeclarativeI65I74WhereEntry450

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.Fixture
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open RetainedFull445
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeGraphRows321 (literal_head)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration Clause)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open CommonRoleOutermostResolver (Tree)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)

def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩

def goodClause : Clause := ⟨40,8,[.var 11],[]⟩
def badClause : Clause := ⟨41,9,[.var 12],[]⟩
def lastClause : Clause := ⟨42,10,[.var 11],[]⟩
def implParent (clauses : List Clause) : Declaration :=
  ⟨89,7,[.app 90 [.var 11],.app 90 [.var 12]],clauses,[],[]⟩
def implGood : Declaration := ⟨88,8,[.app 90 [.var 13]],[],[],[]⟩
def implLast : Declaration := ⟨87,10,[.app 90 [.var 14]],[],[],[]⟩

def surface (clauses : List Clause) : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,2,[]⟩,⟨8,1,[]⟩,⟨9,1,[]⟩,⟨10,1,[]⟩]⟩,
    [implParent clauses,implGood,implLast]⟩

def rootEdge (x y : Nat) : Equation := ⟨x,.nominal 90 [.variable y]⟩
def selfAtom (x : Nat) : Atom Nat := .tyLe (.var x) (.var x)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[selfAtom 1,selfAtom 6,selfAtom 4],[]⟩,
    [rootEdge 0 1,rootEdge 1 4,rootEdge 5 6,rootEdge 6 6,rootEdge 4 4]⟩

def parentRaw : GeneralDeclarativeHead320.State := { raw with equations := rootEdge 0 0 :: raw.equations }
def brokenChildRaw : GeneralDeclarativeHead320.State := { raw with
  equations := [rootEdge 0 1,rootEdge 1 4,rootEdge 5 6,rootEdge 4 4] }

def build (ordinary : GeneralDeclarativeHead320.State) (clauses : List Clause) : Option FullProblem := do
  let graph ← compile listSource
  let source ← GeneralSourceMetadataBareBundle291.compile (surface clauses)
  let env : Environment := ⟨2,1,0,listSource,graph,source⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],
      [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨1,[44],listPoint410 90 4⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[27,31],⟨7,[point 0,point 5],[]⟩⟩⟩)

def clauses : List Clause := [goodClause,badClause]
def p : FullProblem := (build raw clauses).get (by decide +kernel)
def cycleAtParent : FullProblem := (build parentRaw clauses).get (by decide +kernel)
def onlyPayloadWasCyclic : FullProblem := (build brokenChildRaw clauses).get (by decide +kernel)
def three : FullProblem := (build raw [goodClause,lastClause,badClause]).get (by decide +kernel)
def reversed : FullProblem := (build raw [badClause,goodClause]).get (by decide +kernel)

def cut0 : ExactEscapeWire := ⟨List.range 7,[0,1,2,2,1,2,2]⟩
def cut5 : ExactEscapeWire := ⟨List.range 7,[2,2,2,2,2,0,1]⟩
def cut1 : ExactEscapeWire := ⟨List.range 7,[2,0,2,2,1,2,2]⟩
def parent : ParentWire := ⟨[0,1],[cut0,cut5]⟩
def safe : ChildWire := .leaf ⟨[2],[cut1]⟩
def looping : ChildWire := .raw ⟨0,⟨3,.same,6⟩,[],.same⟩
def wrongRoot : ChildWire := .raw ⟨0,⟨4,.same,4⟩,[],.same⟩
def wire : WhereWire := ⟨parent,[safe,looping]⟩

def expected : Result := ⟨.selected 89 [.selected 88 [],.rejected],.rejected,[]⟩
def expectThree : Result := ⟨.selected 89 [.selected 88 [],.selected 87 [],.rejected],.rejected,[]⟩
def expectReversed : Result := ⟨.selected 89 [.rejected,.selected 88 []],.rejected,[]⟩
def expectParentOnly : Result := ⟨.rejected,.rejected,[]⟩
def expectDropped : Result := ⟨.selected 89 [.rejected],.rejected,[]⟩

def actualParent : ParentSelection p.old :=
  ⟨implParent clauses,(readParentChoice p.old (implParent clauses) rfl parent).get (by decide +kernel)⟩

theorem original_two_requests_use_distinct_binders_and_source_slots450 :
    actualParent.children = [⟨[27,31,0],⟨8,[point 1],[]⟩⟩,⟨[27,31,1],⟨9,[point 6],[]⟩⟩] :=
  rfl

def muState : CommonNominalSyntax.State Common.Row := .block [.nominal 90 [.inl (.inl 0)]] 0
def mu : Ty := .nominal 90 [.inl muState]

theorem mu_matches_real_list450 :
    Equivalent mu (nominal 90 [.inl mu]) := by
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
  ⟨fun _ => (mu,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (listPoint410 90 1)
      else if n = 5 then some (listPoint410 90 6)
      else if n = 1 then some (listPoint410 90 4) else none⟩

theorem exact_where_state_has_a_fitting_model450 : FitsFull p.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    change a ∈ [selfAtom 1,selfAtom 6,selfAtom 4] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro _ empty
    cases empty
  · intro row seen
    change row ∈ [rootEdge 0 1,rootEdge 1 4,rootEdge 5 6,rootEdge 6 6,rootEdge 4 4] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl) <;> exact mu_matches_real_list450
  · intro _ empty; cases empty
  · intro source receipt
    change source ∈ [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩,⟨1,[44],listPoint410 90 4⟩] at receipt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at receipt
    rcases receipt with rfl|rfl|rfl <;> rfl
  · intro _ empty; cases empty

theorem first_child_safe_and_only_second_has_actual_root_K2450 :
    ¬RootCycle p.state.base ⟨[27,31,0],⟨8,[point 1],[]⟩⟩ ∧
      RootCycle p.state.base ⟨[27,31,1],⟨9,[point 6],[]⟩⟩ := by
  constructor
  · rintro ⟨a,which,bad⟩
    cases List.mem_singleton.mp which
    exact SplitEscape446.checked_split_escape_excludes_exact_raw_K2446
      (s := raw) (site := 1) (w := cut1) (by decide +kernel) bad
  · exact GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨3,.same,6⟩,[],.same⟩)
      (by decide +kernel)

theorem actual_parent_cycle_declines_every_wire450 (w : WhereWire) :
    check_full450 cycleAtParent expected (.whereRoot w) = false := by
  apply actual_parent_K2_cannot_be_relabelled_as_child450
  exact GeneralDeclarativeWitnessCycle350.rooted (w := ⟨0,⟨0,.same,0⟩,[],.same⟩)
    (by decide +kernel)

def probe (p : FullProblem) (r : Result) (ws : List ChildWire) : Bool :=
  check_full450 p r (.whereRoot ⟨parent,ws⟩)

/-- info: [true, true, true, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval [probe p expected [safe,looping],probe three expectThree [safe,safe,looping],
  probe reversed expectReversed [looping,safe],probe p expectParentOnly [safe,looping],
  probe cycleAtParent expected [safe,looping],probe p expectDropped [looping],
  probe p expected [looping,safe],probe p expected [safe,wrongRoot],
  probe p expected [safe,looping,safe],probe onlyPayloadWasCyclic expected [safe,looping]]

#print axioms original_two_requests_use_distinct_binders_and_source_slots450
#print axioms exact_where_state_has_a_fitting_model450
#print axioms first_child_safe_and_only_second_has_actual_root_K2450
#print axioms actual_parent_cycle_declines_every_wire450
end Yulang.GeneralDeclarativeI65.I72.WhereSites450.Fixture
