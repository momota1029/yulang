import Yulang.GeneralDeclarativeReplayModels348
import Yulang.GeneralDeclarativeRepeatedRows348
import Yulang.GeneralWhereVersionLeafCommit317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeRepeatedPlacement348
open GeneralWhereVersionInstall317 (fixed before Models)
open GeneralWhereVersionCase317 (site occ lower upper descriptor centers_preserved)
open GeneralWhereVersionCommit317 (framedState)
open GeneralWhereVersionJournal317 (fixed_iff)
open GeneralLiveCompoundChildSite316 (child)
open GeneralDeclarativeReplayCompile348 (output logicalArg)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralDeclarativeReplayModels348 (model_extension where_values)
open GeneralDeclarativeNativeRoot347 (starting_model output_holds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand)
open GeneralStoppedPlacement335 (Meaning)
open GeneralNominalCommonBridge (Assignment)
open GeneralMixedCompoundChildEquality307 (mid)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

noncomputable abbrev keep := [0,2,4,lower,mid,upper,GeneralDictionaryCompoundBase239.lo,
  GeneralDictionaryCompoundBase239.hi] ++ journalSources fixed

theorem same_model (m : Assignment) (fit : Models fixed m) :
    ∃ n, Models fixed n ∧ GeneralDeclarativeHead320.Models (output keep) n ∧
      ∀ k ∈ keep,n k = m k := by
  have original := ((fixed_iff m).mp fit).1
  obtain ⟨n,compiled,agrees⟩ := model_extension keep
    (by exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    m (starting_model m original) (output_holds m original)
  have raw := (journal_models fixed
    (fun k found => (agrees k (List.mem_append_right _ found)).symm)).mp fit
  exact ⟨n,raw,compiled,agrees⟩

noncomputable abbrev nativeArg : Capture := ⟨lower,mid,upper⟩
noncomputable abbrev requested := GeneralDeclarativeReplayCompile348.child keep

theorem modes (m : Assignment) (fit : Models fixed m)
    (compiled : GeneralDeclarativeHead320.Models (output keep) m) :
    Meaning m nativeArg (logicalArg keep) := by
  have known := (GeneralWhereVersionInstall317.mixed_eq ▸ fit.1 :
    GeneralNominalVersionedJournal232.Models framedState m)
  have actual := GeneralWhereVersionLeafCommit317.actual_ports m known
  have center := GeneralWhereVersionLeafCommit317.mid_value m known
  have logical := where_values keep m compiled
  exact ⟨eqv_trans actual.1 (eqv_symm logical.1),eqv_trans center (eqv_symm logical.2.1),
    eqv_trans actual.2 (eqv_symm logical.2.2)⟩

noncomputable def links : List Equation :=
  [⟨lower,.variable (logicalArg keep).lower⟩,⟨mid,.variable (logicalArg keep).center⟩,
    ⟨upper,.variable (logicalArg keep).upper⟩]

noncomputable abbrev placedView := appendFacts (output keep) links

theorem placement_models (m : Assignment) (fit : Models fixed m)
    (compiled : GeneralDeclarativeHead320.Models (output keep) m) :
    GeneralDeclarativeHead320.Models placedView m := by
  have related := modes m fit compiled
  refine (model_append m).mpr ⟨compiled,?_⟩
  intro row inList
  change row ∈ [⟨lower,.variable (logicalArg keep).lower⟩,⟨mid,.variable (logicalArg keep).center⟩,
    ⟨upper,.variable (logicalArg keep).upper⟩] at inList
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inList
  rcases inList with rfl|rfl|rfl
  · exact related.1
  · exact related.2.1
  · exact related.2.2

theorem demand : activeDemand fixed.mixed site = ⟨1,[nativeArg],[]⟩ := by
  have none : GeneralNominalCenteredHeadOutputs.requests fixed.mixed.core occ = [] := by
    rw [GeneralWhereVersionInstall317.mixed_eq]
    cases atReq : GeneralNominalCenteredHeadOutputs.requests framedState.core occ with
    | nil => rfl
    | cons out other =>
      exact False.elim (GeneralWhereVersionLeafRegistry317.no_request out (atReq ▸ List.mem_cons_self))
  unfold activeDemand
  rw [show site.occurrence = occ from rfl,none]
  change GeneralDeclarativeDemand320.Demand.mk _ (List.ofFn (GeneralStoppedOrdinarySite335.argument site)) [] = _
  rw [List.ofFn_succ]
  have original := GeneralWhereVersionCase317.descriptor
  change GeneralDeclarativeDemand320.Demand.mk 1 [GeneralStoppedOrdinarySite335.argument site 0] [] = _
  unfold GeneralStoppedOrdinarySite335.argument
  rw [original,centers_preserved]

/-- Exact role, registered proper occurrence and original output
list; only the three mode-specific logical names may be related by
the independently checked ordinary equations. -/
theorem actual_placement (m : Assignment) (fit : Models fixed m) :
    Placement fixed.mixed placedView occ requested := by
  obtain ⟨appendSite,_,_⟩ := GeneralDeclarativeRepeatedRows348.corrected_position m fit
  refine ⟨site,List.mem_iff_getElem?.mpr ⟨2,appendSite⟩,rfl,?_⟩
  rw [demand]
  exact ⟨rfl,.cons ⟨.forward (List.mem_append_right _ List.mem_cons_self),
    .forward (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    .forward (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩ .nil,rfl⟩

theorem same_model_placement (m : Assignment) (fit : Models fixed m) :
    ∃ n, Models fixed n ∧ GeneralDeclarativeHead320.Models placedView n ∧
      Placement fixed.mixed placedView occ requested ∧
      ∀ k ∈ keep,n k = m k := by
  obtain ⟨n,raw,typed,agrees⟩ := same_model m fit
  exact ⟨n,raw,placement_models n raw typed,actual_placement n raw,agrees⟩

end Yulang.GeneralDeclarativeRepeatedPlacement348
