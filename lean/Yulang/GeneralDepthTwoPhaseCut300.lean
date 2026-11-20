import Yulang.GeneralDepthTwoEvidence300
import Yulang.GeneralGeneratedDictionaryScope299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoPhaseCut300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoMiddleContext300 (after_raw_sites after_center_sites)
open GeneralDepthTwoFinalParents300 (oldRoot)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalExamples (registry intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralGeneratedDictionaryScope299 (all_left)

theorem after_edges : after.core.erased.current.edges = [(root,middle)] :=
  GeneralGeneratedNestedInstallInterface299.only_first_edge rfl

theorem different_phases : initial ≠ after ∧ after ≠ final ∧ initial ≠ final := by
  let edgeCount := fun s : State roles => s.core.erased.current.edges.length
  have first : edgeCount initial = 0 := by
    change initial.core.erased.current.edges.length = 0
    rfl
  have second : edgeCount after = 1 := by
    change after.core.erased.current.edges.length = 1
    rw [after_edges]
    rfl
  have third : edgeCount final = 2 := by
    change final.core.erased.current.edges.length = 2
    rw [GeneralDepthTwoEvidence300.final_edges]
    rfl
  exact ⟨fun h => (by decide : (0 : Nat) ≠ 1) (first.symm.trans ((congrArg edgeCount h).trans second)),
    fun h => (by decide : (1 : Nat) ≠ 2) (second.symm.trans ((congrArg edgeCount h).trans third)),
    fun h => (by decide : (0 : Nat) ≠ 2) (first.symm.trans ((congrArg edgeCount h).trans third))⟩

theorem no_refresh_in_place (ctx : GeneralNominalCandidates.Context) :
    GeneralNominalVersionedRefresh232.refresh initial ctx ≠ after ∧
      GeneralNominalVersionedRefresh232.refresh after ctx ≠ final := by
  constructor <;> intro eq
  · have same := congrArg (fun (s : State roles) => s.core.erased.current.edges) eq
    change [] = after.core.erased.current.edges at same
    rw [after_edges] at same
    cases same
  · have same := congrArg (fun (s : State roles) => s.core.erased.current.edges) eq
    change after.core.erased.current.edges = final.core.erased.current.edges at same
    rw [after_edges,GeneralDepthTwoEvidence300.final_edges] at same
    cases same

theorem after_terminal_frame_absent (p : GeneralNominalCenters.Plan roles) (k : Nat) :
    ¬ Frame compiled after.core terminal k p := by
  intro given
  have raw := given.raw_recorded
  rw [after_raw_sites] at raw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at raw
  rcases raw with eq|eq
  · have eq' : terminal = root := by
      rw [← given.occurrence_eq,eq]
      rfl
    exact GeneralDepthTwoTerminalFrame300.no_alias_terminal_root (congrArg (fun v => v.identity) eq')
  · have eq' : terminal = middle := by
      rw [← given.occurrence_eq,eq]
      exact GeneralDepthTwoRootPlan300.child_data.1
    exact GeneralGeneratedNestedPredictions299.different_occurrences.2
      (congrArg (fun v => v.identity) eq'.symm)

theorem no_terminal_evidence (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m terminal d := by
  intro existsTerm
  have raw : PayloadEvidence (Instance compiled after.core m) terminal d :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr existsTerm
  cases raw with
  | node instance' _ =>
    obtain ⟨p,cert⟩ := instance'
    exact after_terminal_frame_absent p _ cert.frame

theorem no_middle_evidence (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m middle d := by
  intro existsTerm
  have raw : PayloadEvidence (Instance compiled after.core m) middle d :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr existsTerm
  cases raw with
  | node instance' childProofs =>
    obtain ⟨p,cert⟩ := instance'
    cases GeneralDepthTwoSecondInstall300.frame_unique cert.frame
    have one := cert.children_eq.trans GeneralDepthTwoMiddleContext300.same_children
    rw [one] at childProofs
    obtain ⟨data,proof⟩ := all_left childProofs terminal (List.mem_singleton_self _)
    exact no_terminal_evidence m data ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp proof)

theorem second_closes_evidence :
    (boundary roles).Step registry root after final ∧
      (∀ m d, ¬ (boundary roles).Evidence registry after m middle d) ∧
      ∀ m, Models after m →
        Models final m ∧
        (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]]) := by
  exact ⟨GeneralDepthTwoSecondInstall300.actual,no_middle_evidence,
    fun m good =>
      let held := (GeneralDepthTwoSecondInstall300.models m).mpr good
      ⟨held,GeneralDepthTwoEvidence300.root_evidence m held⟩⟩

end Yulang.GeneralDepthTwoPhaseCut300
