import Yulang.GeneralDeclarativeI65I74ListFrameEntry449

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame.TwoActualSites
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open RetainedFull445
open ListSites449 (checkSiteTable)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Descends)
open GeneralDeclarativeGraphRows321 (observed structural literal_head)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open List410 (listPoint410 invariantValue410 ExactEscapeWire)

def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩


def implLen2 : Declaration := ⟨89,7,[.app 90 [.var 11],.app 90 [.var 12]],[],[],[]⟩

def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,2,[]⟩]⟩,[implLen2]⟩

def rootEdge (x y : Nat) : Equation := ⟨x,.nominal 90 [.variable y]⟩
def flat (x y : Nat) : Equation := ⟨x,.variable y⟩
def selfAtom (x : Nat) : Atom Nat := .tyLe (.var x) (.var x)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[selfAtom 1,selfAtom 6],[(2,0),(0,1)]⟩,
    [rootEdge 0 1,rootEdge 0 3,rootEdge 1 1,rootEdge 3 4,flat 1 2,rootEdge 5 6,rootEdge 6 6]⟩

def rawSecondReturn : GeneralDeclarativeHead320.State := { raw with equations := flat 6 5 :: raw.equations }

def build (ordinary : GeneralDeclarativeHead320.State) (second payload : Nat) : Option FullProblem := do
  let graph ← compile listSource
  let source ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,source⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],
      [⟨0,[42],listPoint410 90 1⟩,⟨second,[43],listPoint410 90 payload⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[27],⟨7,[point 0,point second],[]⟩⟩⟩)

def problem : FullProblem := (build raw 5 6).get (by decide +kernel)
def returned : FullProblem := (build rawSecondReturn 5 6).get (by decide +kernel)
def payloadBecomesInspected : FullProblem := (build raw 1 1).get (by decide +kernel)
def cut0 : ExactEscapeWire := ⟨[1,2,0,3,4,5,6],[1,0,1,1,1,2,2]⟩
def cut5 : ExactEscapeWire := ⟨[1,2,0,3,4,5,6],[2,2,2,2,2,0,1]⟩
def wire : FrameWire := ⟨[0,1],[cut0,cut5]⟩
def expected : Result := Check408.nullaryReport implLen2

def originals : ListFrameChoice problem.old implLen2 :=
  (readListFrameChoice problem.old implLen2 rfl wire).get (by decide +kernel)

theorem two_real_captures_have_exact_slots449 :
    originals.roster.bindings = [(11,1),(12,6)] ∧
      problem.root.demand.arguments.map Capture.lower = [0,5] := ⟨rfl,rfl⟩

theorem two_certificates_track_real_positions_not_orderless449 :
    checkSiteTable raw [0,5] [cut0,cut5] = true ∧
      checkSiteTable raw [0,5] [cut5,cut0] = false ∧
      checkSiteTable raw [0,5] [cut0] = false := by decide +kernel

theorem both_payloads_are_real_cycles_but_only_binders449 :
    AliasCycle raw (observed raw) 1 ∧ AliasCycle raw (observed raw) 6 := by
  have loop (i : Nat) (atRow : rootEdge i i ∈ raw.equations) : AliasCycle raw (observed raw) i :=
    ⟨i,i,⟨.nominal 90 [i],literal_head (exp := (rootEdge i i).right) atRow rfl,
      List.mem_cons_self⟩,.refl i,alias_refl i⟩
  exact ⟨loop 1 (by decide +kernel),loop 6 (by decide +kernel)⟩

theorem genuine_return_only_at_second_inspected_site449 :
    ¬AliasCycle rawSecondReturn (observed rawSecondReturn) 0 ∧
      RootCycle returned.state.base returned.root := by
  constructor
  · exact ListSites449.table_only_validates_actual_safe_sites449
      (show checkSiteTable rawSecondReturn [0] [cut0] = true from by decide +kernel) 0 List.mem_cons_self
  · refine ⟨point 5,List.mem_cons_of_mem _ List.mem_cons_self,6,6,
      ⟨.nominal 90 [6],literal_head (exp := (rootEdge 5 6).right) (by decide +kernel) rfl,
        List.mem_cons_self⟩,.refl 6,.forward (by decide +kernel)⟩

theorem a_payload_becomes_relevant_at_an_actual_second_head449 :
    RootCycle payloadBecomesInspected.state.base payloadBecomesInspected.root :=
  ⟨point 1,List.mem_cons_of_mem _ List.mem_cons_self,both_payloads_are_real_cycles_but_only_binders449.1⟩

def muState : CommonNominalSyntax.State Common.Row := .block [.nominal 90 [.inl (.inl 0)]] 0
def mu : Ty := .nominal 90 [.inl muState]

theorem regular_mu_is_same_as_its_real_list_step449 :
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
      else if n = 5 then some (listPoint410 90 6) else none⟩

theorem two_actual_site_snapshot_fits_full449 : FitsFull problem.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    change a ∈ [selfAtom 1,selfAtom 6] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro _ _
    exact CommonNominalFullCarrier.subtype_refl _
  · intro row seen
    change row ∈ [rootEdge 0 1,rootEdge 0 3,rootEdge 1 1,rootEdge 3 4,flat 1 2,
      rootEdge 5 6,rootEdge 6 6] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
      first | exact regular_mu_is_same_as_its_real_list_step449 |
        exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro _ empty; cases empty
  · intro source receipt
    change source ∈ [⟨0,[42],listPoint410 90 1⟩,⟨5,[43],listPoint410 90 6⟩] at receipt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at receipt
    rcases receipt with rfl|rfl <;> rfl
  · intro _ empty; cases empty

theorem real_two_site_request_passes_cumulative_entry449 :
    Frame.check_full449 problem expected (.inspectedFrame wire) = true := by decide +kernel

theorem two_site_report_keeps_exact_both_binders_and_same_dictionary449 :
    ∃ e : Event problem.state.base problem.root,
      e.frame.input 11 = point 1 ∧ e.frame.input 12 = point 6 ∧
      I72.DictionaryEvidence problem.state.base model problem.root (.node 89 []) := by
  let choice : FramedSelection problem.old := ⟨implLen2,originals⟩
  obtain ⟨e,_,_,captured,dict⟩ := exact_framed_selection_assembly449 choice
  exact ⟨e,captured 11 1 (by decide +kernel),captured 12 6 (by decide +kernel),
    dict model two_actual_site_snapshot_fits_full449.1⟩

theorem both_actual_cycles_decline_every_frame_wire449 (w : FrameWire) :
    Frame.check_full449 returned expected (.inspectedFrame w) = false ∧
    Frame.check_full449 payloadBecomesInspected expected (.inspectedFrame w) = false :=
  ⟨any_actual_inspected_root_cycle_declines_frame449 genuine_return_only_at_second_inspected_site449.2 _ w,
   any_actual_inspected_root_cycle_declines_frame449 a_payload_becomes_relevant_at_an_actual_second_head449 _ w⟩

def controls : List Bool :=
  [Frame.check_full449 problem expected (.inspectedFrame wire),
   Frame.check_full449 returned expected (.inspectedFrame wire),
   Frame.check_full449 payloadBecomesInspected expected (.inspectedFrame wire),
   Frame.check_full449 problem expected (.inspectedFrame ⟨[0,1],[cut5,cut0]⟩),
   Frame.check_full449 problem expected (.inspectedFrame ⟨[1,0],[cut0,cut5]⟩),
   Frame.check_full449 problem expected (.inspectedFrame ⟨[0,1],[cut0]⟩),
   Frame.check_full449 problem expected (.inspectedFrame ⟨[0,1],[cut0,cut5,cut0]⟩),
   Frame.check_full449 problem {expected with tree := .ambiguous} (.inspectedFrame wire)]

/-- info: [true, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval controls

#print axioms two_real_captures_have_exact_slots449
#print axioms two_certificates_track_real_positions_not_orderless449
#print axioms both_payloads_are_real_cycles_but_only_binders449
#print axioms genuine_return_only_at_second_inspected_site449
#print axioms a_payload_becomes_relevant_at_an_actual_second_head449
#print axioms two_actual_site_snapshot_fits_full449
#print axioms real_two_site_request_passes_cumulative_entry449
#print axioms two_site_report_keeps_exact_both_binders_and_same_dictionary449
#print axioms both_actual_cycles_decline_every_frame_wire449

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame.TwoActualSites
