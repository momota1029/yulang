import Yulang.GeneralDeclarativeI65I74WhereListPriority411

namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411.SpecX9
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open List410 (ListWire invariantValue410 listPoint410 checkExactEscape)
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
def implShowList : Declaration := ⟨88,7,[.app 90 [.var 3]],[⟨4,7,[.var 3],[]⟩],[],[]⟩
def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.invariant⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[implShowList]⟩

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

def expected : Result := expected411 implShowList
def parentWire : ListWire := ⟨0,⟨[0,1],[0,1]⟩⟩
def payloadCycleWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,1⟩,[],.same⟩

def wire : CycleWire := ⟨parentWire,payloadCycleWire⟩

def test (p : Option Problem := problem) (r : Result := expected)
    (tag : Witness := .whereChild wire) : Bool :=
  (p.map fun data => check data r tag).getD false

theorem x9_payload_is_really_on_a_cycle411 :
    GeneralDeclarativePriority321.RootRecurs ordinary payloadRequest :=
  GeneralDeclarativeWitnessCycle350.rooted (w := payloadCycleWire) (by decide +kernel)

theorem x9_root_really_descends_into_that_payload411 :
    GeneralDeclarativeK2Graph321.Descends
      (GeneralDeclarativeGraphRows321.structural ordinary) 0 1 :=
  ⟨.nominal 90 [1],GeneralDeclarativeGraphRows321.literal_head (exp := rootRow.right) (by decide +kernel) rfl,
    List.mem_cons_self⟩

/-- The very same cyclic snapshot has a model in the regular carrier,
not just an unsatisfiable graph on which the semantic claim is vacuous. -/
def muState : CommonNominalSyntax.State Common.Row := by
  exact .block [.variant 8 (.inl 0)] 0

def mu : Ty := .variant 8 muState

theorem mu_observations_unfold411 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (variant 8 mu) := by
  cases depth <;> rfl

theorem mu_is_equivalent_to_its_real_unfolding411 :
    Equivalent mu (variant 8 mu) := by
  constructor
  · intro depth
    rw [← mu_observations_unfold411 depth]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro depth
    rw [← mu_observations_unfold411 depth]
    exact CommonNominalFullDemand.producerLe_refl _

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then nominal 90 [.inl mu] else mu),Common.rowEmpty),
    fun _ => none, fun n => if n = 0 then some (listPoint410 90 1) else none⟩

theorem x9_exact_cyclic_input_fits_its_model411 {p : Problem} (got : problem = some p) :
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
        · exact mu_is_equivalent_to_its_real_unfolding411
      · intro _ empty; cases empty
      · intro item inList
        have eq : item = (⟨0,[42],listPoint410 90 1⟩ : GeneralDeclarativeI65.Origin) :=
          List.mem_singleton.mp inList
        cases eq
        rfl

theorem x9_exact_tree_check_returns_true411 : test = true := by decide +kernel

theorem x9_parent_is_not_raw_root_K2411 :
    ¬ GeneralDeclarativePriority321.RootRecurs ordinary request := by
  rintro ⟨a,mem,c⟩
  change a ∈ [⟨0,0,0⟩] at mem
  cases List.mem_singleton.mp mem
  exact List410.exact_escape_refutes_raw_root_K2410
    (w := parentWire.escape) (by decide +kernel) c

theorem x9_parent_only_rejection_and_selected_leaf_both_refused411 :
    test problem Check408.rawReport = false ∧
    test problem (Check408.nullaryReport implShowList) = false ∧
    test problem expected (.previous (.listLeaf parentWire)) = false ∧
    test problem Check408.rawReport (.previous (.previous (.previous (.rawRoot payloadCycleWire)))) = false := by
  decide +kernel

def rewriteOrdinary (p : Problem) (raw : GeneralDeclarativeHead320.State) : Problem :=
  let state := {p.state.core with current := {p.state.core.current with ordinary := raw}}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

def noChildLoop : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow]}

def withParentReturn : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ⟨1,.variable 0⟩ :: ordinary.equations}

def rootReturnWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,1⟩,[],.forward 0⟩

theorem x9_raw_return_keeps_priority_at_actual_parent411 :
    test (problem.map (fun p => rewriteOrdinary p withParentReturn)) = false ∧
    test (problem.map (fun p => rewriteOrdinary p withParentReturn)) Check408.rawReport
      (.previous (.previous (.previous (.rawRoot rootReturnWire)))) = true := by
  decide +kernel

theorem x9_noncyclic_or_counterfeit_child_witness_refused411 :
    test (problem.map (fun p => rewriteOrdinary p noChildLoop)) = false ∧
    test problem expected (.whereChild ⟨parentWire,rootReturnWire⟩) = false ∧
    test problem expected (.whereChild ⟨⟨1,parentWire.escape⟩,payloadCycleWire⟩) = false ∧
    test problem {expected with tree := .selected 99 [.rejected]} = false := by
  decide +kernel

theorem x9_rejection_tree_has_same_cyclic_model_evidence411 :
    ∃ p, problem = some p ∧ check p expected (.whereChild wire) = true ∧
      I72.Fits p.state model ∧ ReportEvidence p.state model p.root expected := by
  have yes := x9_exact_tree_check_returns_true411
  unfold test at yes
  cases got : problem with
  | none => simp [got] at yes
  | some p =>
    have accepted : check p expected (.whereChild wire) = true := by simpa [got] using yes
    have fit := x9_exact_cyclic_input_fits_its_model411 got
    exact ⟨p,rfl,accepted,fit,(check_sound p expected _ accepted).2 model fit⟩

theorem x9_rejected_child_really_occurs_below_show_411 {p : Problem} (q : problem = some p) :
    ∃ (event : Event p.state p.root) (child : I72.Request),
      event.frame.decl = implShowList ∧ event.kids = [child] ∧
      child.occurrence = [27,0] ∧ child.demand = payloadRequest ∧
      ¬RootCycle p.state p.root ∧ RootCycle p.state child := by
  have yes := x9_exact_tree_check_returns_true411
  unfold test at yes
  simp only [q,Option.map_some,Option.getD_some] at yes
  have root : p.root = (⟨[27],request⟩ : I72.Request) := by
    unfold problem at q
    cases sparse : compile bodies with
    | none => simp [sparse] at q
    | some sem =>
      cases authored : GeneralSourceMetadataBareBundle291.compile surface with
      | none => simp [sparse,authored] at q
      | some tbl =>
        simp only [sparse,authored,Option.pure_def] at q
        cases q
        rfl
  obtain ⟨row,scope,source,replay,_cycle,_report⟩ :=
    accepted_where_wire_reflects_actual_child411 p expected wire yes
  have rowEq : visible p.state.core p.root = [implShowList] := by
    unfold problem at q
    cases sparse : compile bodies with
    | none => simp [sparse] at q
    | some sem =>
      cases authored : GeneralSourceMetadataBareBundle291.compile surface with
      | none => simp [sparse,authored] at q
      | some tbl =>
        simp only [sparse,authored,Option.pure_def] at q
        cases q
        have projections : tbl.declarations = surface.declarations :=
          congrArg InputBundle.declarations
            (GeneralSourceMetadataBareBundle291.preserves_input surface tbl authored).1
        rw [show visible _ _ = tbl.declarations.filter (fun d => d.role == 7) from rfl]
        rw [projections]
        rfl
  -- Use the exact operational replay to identify the witness datum in
  -- the resolved input, then reflect that same authored child.
  have same := (List.cons.inj (scope.symm.trans rowEq)).1
  subst row
  have childAt : source.known.child = (⟨[27,0],payloadRequest⟩ : I72.Request) := by
    -- Checked equations pin the original source, not the report structure.
    have originAt : p.state.core.origins = [⟨0,[42],listPoint410 90 1⟩] := by
      unfold problem at q
      cases sparse : compile bodies with
      | none => simp [sparse] at q
      | some sem =>
        cases authored : GeneralSourceMetadataBareBundle291.compile surface with
        | none => simp [sparse,authored] at q
        | some tbl =>
          simp only [sparse,authored,Option.pure_def] at q
          cases q
          rfl
    have member := source.known.authored
    rw [originAt] at member
    have endpoint := source.known.endpoint
    rw [List.mem_singleton.mp member] at endpoint
    have payloadSame : source.known.payload = 1 := by
      change listPoint410 90 1 = listPoint410 source.known.key source.known.payload at endpoint
      injection endpoint with _ span
      injection span with one _
      injection one with pt
      injection pt with o
      injection o with v
      injection v with n
      exact n.symm
    unfold WhereListHead.child WhereListHead.childDemand
    rw [payloadSame,source.known.whereRole,root]
    rfl
  obtain ⟨e,_,sameDecl,exactKids,_,_⟩ := selected_where_is_exact_actual_child411 source
  have raw : RootCycle p.state source.known.child := _cycle
  rw [childAt] at exactKids raw
  exact ⟨e,⟨[27,0],payloadRequest⟩,sameDecl,exactKids,rfl,rfl,source.rawSafe,raw⟩

-- Exact executable branch controls, independent of model construction.
#eval [test,
  test problem Check408.rawReport,
  test problem (Check408.nullaryReport implShowList),
  test problem expected (.previous (.listLeaf parentWire)),
  test (problem.map (fun p => rewriteOrdinary p noChildLoop)),
  test (problem.map (fun p => rewriteOrdinary p withParentReturn)),
  test (problem.map (fun p => rewriteOrdinary p withParentReturn)) Check408.rawReport
    (.previous (.previous (.previous (.rawRoot rootReturnWire)))),
  test problem expected (.whereChild ⟨parentWire,rootReturnWire⟩),
  test problem expected (.whereChild ⟨⟨1,parentWire.escape⟩,payloadCycleWire⟩),
  test problem {expected with tree := .selected 99 [.rejected]}]

#print axioms x9_rejected_child_really_occurs_below_show_411
#print axioms x9_payload_is_really_on_a_cycle411
#print axioms x9_root_really_descends_into_that_payload411
#print axioms mu_observations_unfold411
#print axioms mu_is_equivalent_to_its_real_unfolding411
#print axioms x9_exact_cyclic_input_fits_its_model411
#print axioms x9_exact_tree_check_returns_true411
#print axioms x9_parent_is_not_raw_root_K2411
#print axioms x9_parent_only_rejection_and_selected_leaf_both_refused411
#print axioms x9_raw_return_keeps_priority_at_actual_parent411
#print axioms x9_noncyclic_or_counterfeit_child_witness_refused411
#print axioms x9_rejection_tree_has_same_cyclic_model_evidence411

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411.SpecX9
