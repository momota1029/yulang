import Yulang.GeneralRebaseDepthCrossWitness286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralRebaseDepthPhase286
open GeneralDictionaryOutputDepth252 (roles root registry)
open GeneralDictionaryOutputDepthInstall252 (installed smallModel small_source)
open GeneralRebaseDepthPreAnchor286 (initial)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralRebaseDepthPathEvidence285 (Witness)
open GeneralRebaseDepthCrossWitness286 (kept_of_witness)

abbrev PreAnchor := GeneralRebaseDepthPreAnchor286.Anchor
abbrev PreKept := GeneralRebaseDepthPrePlan286.Kept

structure Pre (s : State roles) : Prop where
  anchor : PreAnchor s
  plan : PreKept s

structure Post (s : State roles) : Prop where
  anchor : GeneralRebaseDepthPathAnchor285.Anchor s
  witness : Witness s
  aliases : s.core.erased.current.aliases = []

theorem start : Pre initial :=
  ⟨GeneralRebaseDepthPreAnchor286.start,GeneralRebaseDepthPrePlan286.start⟩

theorem exclusive {s : State roles} (a : Pre s) (b : Post s) : False := by
  have check := (GeneralRebaseDepthGroundModels285.source_inputs smallModel).mp small_source
  have impossible := (GeneralRebaseDepthGroundModels285.final_check smallModel).mp
    ((b.anchor.models smallModel).mp ((a.anchor.models smallModel).mpr check))
  exact GeneralRebaseDepthMinimal285.scalar_ne_output impossible.2

inductive InstallHop : State roles → State roles → Prop
 | take {s : State roles} (e : Effect roles) (yes : Installable registry s e)
    (sameRoot : e.plan.packet.site.occurrence = root) (novel : ¬ Committed s e.plan) :
    InstallHop s (install s e)

abbrev Hop := GeneralRebaseDepthPathRank285.Hop

theorem pre_partition {s t : State roles} (before : Pre s) (action : Step registry root s t) :
    Hop s t ∨ InstallHop s t := by
  obtain ⟨focus,reachable,operation⟩ := action
  have a := before.anchor
  have same := GeneralNominalVersionedMixedTerminalStable234.generated_only a.sites a.edges reachable
  cases operation with
  | administrative kind =>
    cases kind with
    | enqueue _ absent => exact False.elim (absent _ (a.sites ▸ List.mem_singleton_self _) same.symm)
    | refresh ctx cert n already old new => exact Or.inl (.refresh ctx cert n already old new)
    | equate first last one two equal novel =>
      exact False.elim (novel (GeneralRebaseDepthPreAnchor286.equality_closed a first last one two equal))
    | reobserve revision _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision a.point revision improves)
  | refresh _ ctx cert n already old new => exact Or.inl (.refresh ctx cert n already old new)
  | install e allowed novel => exact Or.inr (.take e allowed same novel)
  | merge first last one two _ novel =>
    rw [a.centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact False.elim (novel (.refl _))

theorem as_step {s t : State roles} (hit : InstallHop s t) : Step registry root s t := by
  cases hit with
  | take e allowed same novel =>
    exact ⟨root,.root,same ▸ GeneralNominalVersionedMixedKernel234.At.install e allowed novel⟩

theorem pre_refresh {s t : State roles} (before : Pre s) (hop : Hop s t) : Pre t := by
  cases hop with
  | refresh ctx cert _ _ _ _ =>
    exact ⟨GeneralRebaseDepthPreAnchor286.advance before.anchor ctx cert,
      GeneralRebaseDepthPrePlan286.advance before.anchor before.plan ctx cert⟩

theorem cross {s t : State roles} (before : Pre s) (hop : InstallHop s t) : Post t := by
  cases hop with
  | take e offered same _ =>
    exact ⟨GeneralRebaseDepthCrossAnchor286.anchored before.anchor before.plan offered same,
      GeneralRebaseDepthCrossWitness286.witness before.anchor before.plan offered same,
      GeneralRebaseDepthCrossAnchor286.aliases before.anchor e⟩

theorem post_step {s t : State roles} (after : Post s) (step : Step registry root s t) : Hop s t :=
  (GeneralRebaseDepthPathRank285.exact after.anchor (kept_of_witness after.witness)).mp step

theorem post_refresh {s t : State roles} (after : Post s) (hop : Hop s t) : Post t := by
  cases hop with
  | refresh ctx cert _ _ _ _ =>
    exact ⟨GeneralRebaseDepthPathAnchor285.next after.anchor ctx cert,
      GeneralRebaseDepthPathEvidence285.witness_next after.anchor after.witness ctx cert,after.aliases⟩

def Covered (s : State roles) : Prop := Pre s ∨ Post s

theorem covered_next {s t : State roles} (was : Covered s) (step : Step registry root s t) : Covered t := by
  rcases was with pre|post
  · rcases pre_partition pre step with located|install
    · exact Or.inl (pre_refresh pre located)
    · exact Or.inr (cross pre install)
  · exact Or.inr (post_refresh post (post_step post step))

theorem path_covered {s t : State roles} {count : Nat}
    (was : Covered s) (path : GeneralRebaseDepthPathRank285.ActualPath s t count) : Covered t := by
  induction path with
  | empty => exact was
  | more _ step ih => exact covered_next ih step

theorem installed_post : Post installed :=
  ⟨GeneralRebaseDepthPathAnchor285.initial,GeneralRebaseDepthPathEvidence285.witness_start,rfl⟩

end Yulang.GeneralRebaseDepthPhase286
