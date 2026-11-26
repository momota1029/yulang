import Yulang.GeneralDeclarativeI65I74ListSiteEntry449

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Spec
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open RetainedFull445
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeGraphRows321 (observed structural literal_head)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile lookup)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal)
open GeneralDeclarativeWitnessRank350 (rank)
open List410 (listPoint410 invariantValue410 ExactEscapeWire checkExactEscape aliasRanks colour)
open SplitEscape446

/-- A recursively declared list shape, with real value occurrence and
recursive named tail. Its mode is obtained from the authored body. -/
def listSource : Source 2 1 0 :=
  ⟨[⟨90,[(.value,0)]⟩],
    (fun node => if node.val = 0 then .union .emptyRecord (.pair (.inr 0) (.inl 1))
      else .nominal 90 [.inl (.inr 0)]),fun _ => 0⟩

theorem recursive_list_has_declared_invariant_value449 :
    (compile listSource).bind (fun made => lookup made 90) = some [invariantValue410] := by
  decide +kernel

def implLen : Declaration := ⟨88,7,[.app 90 [.var 11]],[],[],[]⟩
def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[implLen]⟩

def rootFirst : Equation := ⟨0,.nominal 90 [.variable 1]⟩
def rootOther : Equation := ⟨0,.nominal 90 [.variable 3]⟩
def payloadLoop : Equation := ⟨1,.nominal 90 [.variable 1]⟩
def offBranch : Equation := ⟨3,.nominal 90 [.variable 4]⟩
def sharedAlias : Equation := ⟨1,.variable 2⟩
def returnAlias : Equation := ⟨1,.variable 0⟩
def selfAtom : Atom Nat := .tyLe (.var 1) (.var 1)
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[selfAtom],[(2,0),(0,1)]⟩,[rootFirst,rootOther,payloadLoop,offBranch,sharedAlias]⟩
def rawReturn : GeneralDeclarativeHead320.State := { raw with equations := returnAlias :: raw.equations }

def input : Capture := ⟨0,0,0⟩
def direct : Origin := ⟨0,[42],listPoint410 90 1⟩

def build (ordinary : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile listSource
  let source ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨2,1,0,listSource,graph,source⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨env,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],[direct],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[27],⟨7,[input],[]⟩⟩⟩)

def problem : FullProblem := (build raw).get (by decide +kernel)
def returned : FullProblem := (build rawReturn).get (by decide +kernel)
def escape : ExactEscapeWire := ⟨[1,2,0,3,4],[1,0,1,1,1]⟩
def wire : Wire := ⟨0,[escape]⟩
def expected : Result := Check408.nullaryReport implLen

theorem split_table_escapes_original_root449 :
    checkSiteTable raw [0] [escape] = true := by decide +kernel

theorem two_original_structural_children449 :
    Descends (structural raw) 0 1 ∧ Descends (structural raw) 0 3 := by
  exact ⟨⟨.nominal 90 [1],literal_head (exp := rootFirst.right)
      (by decide +kernel) rfl,List.mem_cons_self⟩,
    ⟨.nominal 90 [3],literal_head (exp := rootOther.right)
      (by decide +kernel) rfl,List.mem_cons_self⟩⟩

theorem uninspected_payload_is_really_on_raw_cycle449 :
    AliasCycle raw (observed raw) 1 :=
  ⟨1,1,⟨.nominal 90 [1],literal_head (exp := payloadLoop.right)
      (by decide +kernel) rfl,List.mem_cons_self⟩,.refl 1,alias_refl 1⟩

theorem tested_root_is_really_not_on_cycle449 :
    ¬AliasCycle raw (observed raw) 0 :=
  table_only_validates_actual_safe_sites449 split_table_escapes_original_root449 0 List.mem_cons_self

theorem previous_tied_grade_certificate_cannot_certify_this_site449
    (old : ExactEscapeWire) : checkExactEscape raw 0 old = false := by
  cases yes : checkExactEscape raw 0 old with
  | false => rfl
  | true =>
    obtain ⟨rankCheck,rootCheck⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp yes).1
    have inequalities := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp rankCheck).1).2
    have lo : rank old.ranks 2 ≤ rank old.ranks 0 :=
      of_decide_eq_true (List.all_eq_true.mp inequalities (2,0) List.mem_cons_self)
    have hi : rank old.ranks 0 ≤ rank old.ranks 1 :=
      of_decide_eq_true (List.all_eq_true.mp inequalities (0,1)
        (List.mem_cons_of_mem _ List.mem_cons_self))
    have tied : rank old.ranks 1 = rank old.ranks 2 :=
      List410.aliasRanks_eq_on_original_alias410 rankCheck (.forward (by decide +kernel))
    have same : rank old.ranks 0 = rank old.ranks 1 :=
      Nat.le_antisymm hi (tied.symm ▸ lo)
    have sideEq : old.side 0 = old.side 1 := congrArg (colour old.palette) same
    have root : old.side 0 = 0 := of_decide_eq_true rootCheck
    have child := List410.exact_escape_tracks_original_edge410 yes (by simp [root])
      two_original_structural_children449.1
    rw [root,child] at sideEq
    cases sideEq

theorem real_alias_return_puts_root_on_cycle449 :
    RootCycle returned.state.base returned.root := by
  refine ⟨input,List.mem_cons_self,1,1,?_,.refl 1,?_⟩
  · exact ⟨.nominal 90 [1],literal_head (exp := rootFirst.right)
      (by decide +kernel) rfl,List.mem_cons_self⟩
  · exact .forward (by decide +kernel)

theorem real_alias_return_refuses_every_new_wire449 (w : Wire) :
    check_full449 returned expected (.inspectedList w) = false :=
  original_root_cycle_declines_all_list_wires449 real_alias_return_puts_root_on_cycle449 _ _

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
    fun n => if n = 0 then some (listPoint410 90 1) else none⟩

theorem real_branching_snapshot_is_nonvacuously_fitting449 : FitsFull problem.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a used
    have eq : a = selfAtom := List.mem_singleton.mp used
    subst a
    exact CommonNominalFullCarrier.subtype_refl _
  · intro interval used
    exact CommonNominalFullCarrier.subtype_refl _
  · intro row remembered
    change row ∈ [rootFirst,rootOther,payloadLoop,offBranch,sharedAlias] at remembered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at remembered
    rcases remembered with (rfl|rfl|rfl|rfl|rfl)
    · exact regular_mu_is_same_as_its_real_list_step449
    · exact regular_mu_is_same_as_its_real_list_step449
    · exact regular_mu_is_same_as_its_real_list_step449
    · exact regular_mu_is_same_as_its_real_list_step449
    · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro _ empty; cases empty
  · intro original stored
    cases List.mem_singleton.mp stored
    rfl
  · intro _ empty; cases empty

theorem actual_list_selection_passes_cumulative_entry449 :
    check_full449 problem expected (.inspectedList wire) = true := by decide +kernel

theorem same_fitting_model_reports_original_list_selection449 :
    Opaque448.Whole.ReportEvidence448 problem model expected :=
  (check_full_sound449 _ _ _ actual_list_selection_passes_cumulative_entry449).2 _
    real_branching_snapshot_is_nonvacuously_fitting449

theorem actual_same_fit_has_exact_list_capture_and_dictionary449 :
    ∃ a : LocalChoice problem,
      a.source.known.capture a.source.known.binder =
        GeneralDeclarativeWitnessDeclaredState357.point 1 ∧
      I72.DictionaryEvidence problem.state.base model problem.root (.node 88 []) := by
  obtain ⟨a,report,read⟩ := accepted_list_report_reads_exact_declaration449
    actual_list_selection_passes_cumulative_entry449
  have declExact : a.decl = implLen :=
    List.singleton_inj.mp (a.source.known.only.symm.trans (show visible problem.state.base.core problem.root =
      [implLen] from rfl))
  have pExact : a.source.known.payload = 1 := by
    have actualOrigin := List.mem_singleton.mp a.source.known.authored
    have source := a.source.known.endpoint
    rw [actualOrigin] at source
    exact Core.PresenceGeneration.TyTerm.var.inj
      (CommonRecursiveNominalIntervals.Endpoint.ordinary.inj
        (CommonRecursiveNominalIntervals.Bounds.point.inj
          (Sum.inl.inj (List.singleton_inj.mp
            (CommonRecursiveNominalIntervals.Endpoint.nominal.inj source.symm).2))))
  have related := List410.exact_report_is_R2_classification410 (List410.list_choice_has_exact_R2_report410 a.source)
  have semantic := List410.dictionary_sound_R2 _ _ _ related model real_branching_snapshot_is_nonvacuously_fitting449.1
  exact ⟨a,by simp [List410.InvariantListHead.capture,pExact],by simpa [declExact,Check408.nullaryReport,implLen,FullProblem.old] using semantic⟩

def probes : List Bool :=
  [check_full449 problem expected (.inspectedList wire),
   check_full449 returned expected (.inspectedList wire),
   check_full449 problem expected (.inspectedList ⟨1,[escape]⟩),
   check_full449 problem expected (.inspectedList ⟨0,[]⟩),
   check_full449 problem expected (.inspectedList ⟨0,[escape,escape]⟩),
   check_full449 problem {expected with tree := .ambiguous} (.inspectedList wire)]

/-- info: [true, false, false, false, false, false] -/
#guard_msgs in
#eval probes

#print axioms recursive_list_has_declared_invariant_value449
#print axioms two_original_structural_children449
#print axioms uninspected_payload_is_really_on_raw_cycle449
#print axioms tested_root_is_really_not_on_cycle449
#print axioms previous_tied_grade_certificate_cannot_certify_this_site449
#print axioms real_alias_return_puts_root_on_cycle449
#print axioms real_alias_return_refuses_every_new_wire449
#print axioms regular_mu_is_same_as_its_real_list_step449
#print axioms real_branching_snapshot_is_nonvacuously_fitting449
#print axioms actual_list_selection_passes_cumulative_entry449
#print axioms same_fitting_model_reports_original_list_selection449
#print axioms actual_same_fit_has_exact_list_capture_and_dictionary449

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Spec
