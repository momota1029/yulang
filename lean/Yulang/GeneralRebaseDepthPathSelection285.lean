import Yulang.GeneralRebaseDepthPathEvidenceAt285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathSelection285
open GeneralDictionaryOutputDepth252 (sourceRegistry registry root roles declaration model)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralRebaseDepthPathAnchor285 (Anchor snapshot)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPathEvidence285 (Witness witness_any)
open GeneralRebaseDepthPathEvidenceAt285 (kept_survivor)

theorem semantic_clear {s : State roles} (a : Anchor s) (o) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s o := by
  have modelEq : Models s = Models installed := funext fun m => propext (a.models m)
  exact fun denied => GeneralRebaseInstalledOutputCycles271.no_cycle _
    ((GeneralNominalVersionedCycles232.full_models_only modelEq).mp denied)

theorem raw_clear {s : State roles} (a : Anchor s) (slot : Fin (snapshot s).base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (snapshot s) slot := by
  intro recognized
  exact semantic_clear a _ (GeneralRebaseRawIntoFull271.recurs s
    ⟨model,GeneralRebaseDepthPathAnchor285.valid_model a.models⟩ slot recognized)

theorem administrative {s : State roles} (a : Anchor s) (w : Witness s) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady s root := by
  obtain ⟨p,f,_,_,_,_⟩ := w
  constructor
  · exact ⟨p.input,f.center_recorded,p.input_exact.trans f.occurrence_eq⟩
  · intro first one _ last two _
    rw [a.centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe {s : State roles} (a : Anchor s) (w : Witness s) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry s root := by
 refine ⟨(kept_survivor a w).1,?_,?_,?_⟩
 · rintro (raw | (⟨_,cycle⟩ | ⟨_,_,_,_,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
     exact raw_clear a slot cycle
   · exact semantic_clear a _ cycle
   · exact semantic_clear a _ cycle
 · rintro (raw | ⟨_,_,_,_,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
     exact raw_clear a visited.1 cycle
   · exact semantic_clear a _ cycle
 · rintro (⟨_,d,visible,_,_,unprepared⟩ | missing)
   · obtain ⟨p,f,_,_,_,_⟩ := w
     have same := (List.mem_singleton.mp visible).trans (List.mem_singleton.mp f.visible).symm
     exact unprepared (same.symm ▸ f.prepared)
   · exact missing (administrative a w)

theorem aliases_empty {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    s.core.erased.current.aliases = [] := by
  induction path with
  | empty => rfl
  | more prior action ih =>
    have w := witness_any prior
    have hop := (GeneralRebaseDepthPathRank285.exact w.1 w.2.1).mp action
    cases hop with
    | refresh ctx _ _ _ _ _ => exact ih

theorem no_merged {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict s root := by
  rintro ⟨⟨a,b,member,_,_⟩,_⟩
  change (a,b) ∈ s.core.erased.current.aliases at member
  rw [aliases_empty path] at member
  cases member

theorem selected {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    Local sourceRegistry s root (.selected 0 []) := by
  have w := witness_any path
  have survive := kept_survivor w.1 w.2.2
  have uniq : GeneralNominalVersionedCandidates231.Unique registry s.core.erased.current.context root 0 [] := by
    refine ⟨survive,?_⟩
    intro key kids other
    have copy := other
    obtain ⟨_,d,visible,_,key_eq,_,_,_,_,_⟩ := other
    cases List.mem_singleton.mp visible
    have equal : key = 0 := key_eq.symm
    subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
      GeneralDictionaryOutputDepth252.checked copy survive⟩
  have knownSafe := safe w.1 w.2.2
  obtain ⟨p,frame,_,done,ready,_⟩ := w.2.2
  have valid := GeneralRebaseDepthPathAnchor285.valid_model w.1.models
  have facts := done.1 model valid
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model knownSafe uniq valid frame ready
    facts.1 (frame.occurrence_eq ▸ facts.2) (no_merged path)

end Yulang.GeneralRebaseDepthPathSelection285
