import Yulang.GeneralRebaseDepthEnableSafety286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29900
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthPreAvailable286
open GeneralDictionaryOutputDepth252 (roles root registry model plan)
open GeneralRebaseDepthPreAnchor286 (Anchor initial)
open GeneralRebaseDepthPrePlan286 (Certified)
open GeneralRebaseDepthEnableShape286 (Linked Shape as_pre)
open GeneralRebaseDepthEnableSafety286 (unique safe cache positions)
open GeneralRebaseDepthPhase286 (Pre Post Hop InstallHop)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed Step)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralRebaseDepthPathRank285 (ActualPath)

theorem alternative_safety {s : State roles} {p : Plan roles} (a : Anchor s)
    (v : Certified s p) (shape : Shape p) :
    GeneralNominalVersionedMixedKernel234.AlternativesSafe registry s p.input := by
  intro q _ frame
  have atRoot := p.input_exact.trans v.frame.occurrence_eq
  rw [atRoot] at frame
  have eq := GeneralRebaseDepthPreInstall286.unique_located a
    (GeneralRebaseDepthPathKeep285.of_frame frame)
    (GeneralRebaseDepthPathKeep285.of_frame v.frame)
  subst q
  exact positions a shape

noncomputable def candidate {s : State roles} {p : Plan roles}
    (a : Anchor s) (v : Certified s p) : Effect roles := by
  refine ⟨registry,s.core,p,?_,?_,?_⟩
  · have f := v.frame
    rw [← v.frame.occurrence_eq,← v.frame.key_eq] at f
    exact f
  · rw [v.frame.occurrence_eq,v.frame.key_eq,v.leaf]
    exact unique a v
  · rw [v.frame.occurrence_eq]
    exact v.ready

theorem candidate_enabled {s : State roles} {p : Plan roles} (a : Linked s)
    (v : Certified s p) (shape : Shape p) : Installable registry s (candidate a.anchor v) := by
  refine ⟨rfl,rfl,?_,cache a,?_,?_,positions a.anchor shape,alternative_safety a.anchor v shape,?_⟩
  · change B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry s
      p.packet.site.occurrence
    rw [v.frame.occurrence_eq]
    exact safe a.anchor v
  · change (GeneralNominalVersionedPlans231.emittedSchema p).unknown = false
    rw [shape.emitted,GeneralDictionaryOutputDepth252.emitted_exact]
  · intro other membership _
    rw [a.packets] at membership
    cases membership
  · refine ⟨model,(GeneralRebaseDepthPreInstall286.installation_check
      (e := candidate a.anchor v) a.anchor v rfl v.frame.occurrence_eq model).mpr ?_⟩
    exact (GeneralRebaseDepthPrePlan286.unrelated_output model).mp
      ⟨GeneralRebaseDepthPrePlan286.example_check,GeneralDictionaryOutputDepth252.output_valid⟩

theorem offers {s : State roles} (a : Linked s) : ∃ t, InstallHop s t := by
  obtain ⟨p,v,shape⟩ := a.witness
  exact ⟨_,.take (candidate a.anchor v) (candidate_enabled a v shape) v.frame.occurrence_eq
    (GeneralRebaseDepthPreInstall286.genuinely_novel a.anchor v)⟩

def ReachableClass (s : State roles) : Prop := Linked s ∨ Post s

theorem step {s t : State roles} (a : ReachableClass s) (taken : Step registry root s t) : ReachableClass t := by
  rcases a with pre|post
  · rcases GeneralRebaseDepthPhase286.pre_partition (as_pre pre) taken with hop|installation
    · exact Or.inl (GeneralRebaseDepthEnableShape286.hop pre hop)
    · exact Or.inr (GeneralRebaseDepthPhase286.cross (as_pre pre) installation)
  · exact Or.inr (GeneralRebaseDepthPhase286.post_refresh post (GeneralRebaseDepthPhase286.post_step post taken))

theorem reach {s t : State roles} {count : Nat} (a : ReachableClass s)
    (path : ActualPath s t count) : ReachableClass t := by
  induction path with
  | empty => exact a
  | more _ taken ih => exact step ih taken

theorem actual_reach {t : State roles} {count : Nat} (path : ActualPath initial t count) :
    ReachableClass t :=
  reach (Or.inl GeneralRebaseDepthEnableShape286.initial) path

theorem settled_post {t : State roles} {count : Nat} (path : ActualPath initial t count)
    (halted : ∀ dest, ¬ Step registry root t dest) : Post t := by
  rcases actual_reach path with before|after
  · obtain ⟨target,op⟩ := offers before
    exact (halted target (GeneralRebaseDepthPhase286.as_step op)).elim
  · exact after

end Yulang.GeneralRebaseDepthPreAvailable286
