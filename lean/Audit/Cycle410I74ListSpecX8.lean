import Yulang.GeneralDeclarativeI65I74ListEntry410

namespace Yulang.GeneralDeclarativeI65.I72.List410.SpecX8
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal variant)
open PresenceNormalForm (Atom)
open Checker408 (Problem Result)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def implLenList : Declaration := ⟨88,7,[.app 90 [.var 3]],[],[],[]⟩
def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.invariant⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[implLenList]⟩

def rootRow : Equation := ⟨0,.nominal 90 [.variable 1]⟩
def loopRow : Equation := ⟨1,.variant 8 (.variable 1)⟩
def atom : Atom Nat := .tyLe (.var 1) (.var 1)
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[atom],[]⟩,[rootRow,loopRow]⟩
def request : Demand := ⟨7,[⟨0,0,0⟩],[]⟩
def payloadRequest : Demand := ⟨7,[⟨1,1,1⟩],[]⟩

def problem : Option Problem := do
  let graph ← compile bodies
  let resolved ← GeneralSourceMetadataBareBundle291.compile surface
  let environment : Environment := ⟨0,0,0,bodies,graph,resolved⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨environment,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],
      [⟨0,[42],listPoint410 90 1⟩],[]⟩
  let b6 : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,b6⟩,⟨[27],request⟩⟩

def expected : Result := Check408.nullaryReport implLenList
def wire : ListWire := ⟨0,⟨[0,1],[0,1]⟩⟩
def test (p : Option Problem := problem) (r : Result := expected)
    (tag : Witness := .listLeaf wire) : Bool :=
  (p.map fun data => check data r tag).getD false

def payloadCycleWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,1⟩,[],.same⟩

theorem x8_payload_is_really_on_a_cycle410 :
    GeneralDeclarativePriority321.RootRecurs ordinary payloadRequest :=
  GeneralDeclarativeWitnessCycle350.rooted (w := payloadCycleWire) (by decide +kernel)

theorem x8_root_really_descends_into_that_payload410 :
    GeneralDeclarativeK2Graph321.Descends
      (GeneralDeclarativeGraphRows321.structural ordinary) 0 1 :=
  ⟨.nominal 90 [1],GeneralDeclarativeGraphRows321.literal_head (exp := rootRow.right) (by decide +kernel) rfl,
    List.mem_cons_self⟩

theorem x8_no_whole_graph_rank_can_certify410 (levels : List Nat) :
    GeneralDeclarativeWitnessRank350.check ordinary levels = false := by
  cases h : GeneralDeclarativeWitnessRank350.check ordinary levels with
  | false => rfl
  | true =>
    obtain ⟨a,_,cycle⟩ := x8_payload_is_really_on_a_cycle410
    exact False.elim (GeneralDeclarativeTaggedElection340.no_cycles
      (GeneralDeclarativeWitnessRank350.sound h) a.lower cycle)

theorem x8_exact_acyclic_root_positive410 : test = true := by decide +kernel

def realReturn (p : Problem) : Problem :=
  let state := {p.state.core with current := {p.state.core.current with ordinary :=
    {ordinary with equations := ⟨1,.variable 0⟩ :: ordinary.equations}}}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

def realReturnWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,1⟩,[],.forward 0⟩

theorem x8_alias_return_conflicts_with_positive_certificate410 :
    test (problem.map realReturn) = false := by decide +kernel

theorem x8_actual_raw_alias_return_keeps_existing_rejection410 :
    test (problem.map realReturn) Check408.rawReport
      (.previous (.previous (.rawRoot realReturnWire))) = true := by decide +kernel

theorem x8_wrong_report_and_unbacked_certificate_refused410 :
    test problem {expected with tree := .ambiguous} = false ∧
      test problem expected (.listLeaf ⟨1,wire.escape⟩) = false ∧
      test problem expected (.listLeaf ⟨0,⟨[0,1],[0,0]⟩⟩) = false := by
  decide +kernel

/-- Independent graph controls: a one-way bound does not create an alias;
an undecoded join creates no structural edge at all. The earlier sufficient
single-level certificate can fail here without an actual root cycle. -/
def rewriteOrdinary (p : Problem) (raw : GeneralDeclarativeHead320.State) : Problem :=
  let state := {p.state.core with current := {p.state.core.current with ordinary := raw}}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

def oneWay : GeneralDeclarativeHead320.State :=
  {ordinary with normal := {ordinary.normal with intervals := [(1,0)]}}
def unobservedJoin : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ⟨0,.join (.variable 0) (.variable 0)⟩ :: ordinary.equations}

theorem x8_one_way_bound_does_not_make_aliased_return410 :
    checkEscape oneWay 0 [0,1] = false ∧
      test (problem.map (fun p => rewriteOrdinary p oneWay)) expected
        (.listLeaf ⟨0,⟨[1,0],[1,0]⟩⟩) = true := by decide +kernel

theorem x8_unobserved_join_has_no_fabricated_edge410 :
    checkEscape unobservedJoin 0 [0,1] = false ∧
      test (problem.map (fun p => rewriteOrdinary p unobservedJoin)) = true := by decide +kernel

/-- The very same cyclic snapshot has a model in the regular carrier,
not just an unsatisfiable graph on which the semantic claim is vacuous. -/
def muState : CommonNominalSyntax.State Common.Row := by
  exact .block [.variant 8 (.inl 0)] 0

def mu : Ty := .variant 8 muState

theorem mu_observations_unfold410 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (variant 8 mu) := by
  cases depth <;> rfl

theorem mu_is_equivalent_to_its_real_unfolding410 :
    Equivalent mu (variant 8 mu) := by
  constructor
  · intro depth
    rw [← mu_observations_unfold410 depth]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro depth
    rw [← mu_observations_unfold410 depth]
    exact CommonNominalFullDemand.producerLe_refl _

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then nominal 90 [.inl mu] else mu),Common.rowEmpty),
    fun _ => none, fun n => if n = 0 then some (listPoint410 90 1) else none⟩

theorem x8_exact_cyclic_input_fits_its_model410 {p : Problem} (got : problem = some p) :
    I72.Fits p.state model := by
  unfold problem at got
  cases sparse : compile bodies with
  | none => simp [sparse] at got
  | some sem =>
    cases authored : GeneralSourceMetadataBareBundle291.compile surface with
    | none => simp [sparse,authored] at got
    | some tbl =>
      simp only [sparse,authored,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a used
        have eq : a = atom := List.mem_singleton.mp used
        cases eq
        exact CommonNominalFullCarrier.subtype_refl _
      · intro _ empty; cases empty
      · intro e seen
        change e ∈ [rootRow,loopRow] at seen
        have options : e = rootRow ∨ e = loopRow := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using seen
        rcases options with rfl|rfl
        · exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
        · exact mu_is_equivalent_to_its_real_unfolding410
      · intro _ empty; cases empty
      · intro item inList
        have eq : item = (⟨0,[42],listPoint410 90 1⟩ : GeneralDeclarativeI65.Origin) :=
          List.mem_singleton.mp inList
        cases eq
        rfl

theorem x8_selected_dictionary_in_the_cyclic_model410 :
    ∃ p, problem = some p ∧ check p expected (.listLeaf wire) = true ∧
      I72.Fits p.state model ∧ I72.DictionaryEvidence p.state model p.root (.node 88 []) := by
  have yes := x8_exact_acyclic_root_positive410
  unfold test at yes
  cases got : problem with
  | none => simp [got] at yes
  | some p =>
    have accepted : check p expected (.listLeaf wire) = true := by simpa [got] using yes
    have fit := x8_exact_cyclic_input_fits_its_model410 got
    have same := exact_report_is_R2_classification410 (check_sound p expected _ accepted).1
    exact ⟨p,rfl,accepted,fit,dictionary_sound_R2 _ _ _ same model fit⟩

#print axioms x8_payload_is_really_on_a_cycle410
#print axioms x8_root_really_descends_into_that_payload410
#print axioms x8_no_whole_graph_rank_can_certify410
#print axioms x8_exact_acyclic_root_positive410
#print axioms x8_alias_return_conflicts_with_positive_certificate410
#print axioms x8_actual_raw_alias_return_keeps_existing_rejection410
#print axioms x8_wrong_report_and_unbacked_certificate_refused410
#print axioms x8_one_way_bound_does_not_make_aliased_return410
#print axioms x8_unobserved_join_has_no_fabricated_edge410
#print axioms mu_observations_unfold410
#print axioms mu_is_equivalent_to_its_real_unfolding410
#print axioms x8_exact_cyclic_input_fits_its_model410
#print axioms x8_selected_dictionary_in_the_cyclic_model410

end Yulang.GeneralDeclarativeI65.I72.List410.SpecX8
