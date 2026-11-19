import Yulang.GeneralRebaseNonleafTransport276
import Yulang.GeneralRebaseScopedFrame276
import Yulang.GeneralNominalVersionedMixedTerminalStable234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTerminalAbsorb278
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseNonleafTransport276 (ReadyRule)
variable {roles : Roles.RoleDecls}

structure Terminal (r : Registry) (s : State roles) (root : Occurrence roles) : Prop where
  declaration : ∃ d, r.declarations = [d]
  raw : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]
  center : ∃ site, s.core.sites = [site]
  edges : s.core.erased.current.edges = []

def InstallTransition (r : Registry) (root : Occurrence roles) (s t : State roles) : Prop :=
  ∃ e : Effect roles, Generated s.core.erased.current root e.plan.packet.site.occurrence ∧
    Installable r s e ∧ ¬ Committed s e.plan ∧ t = GeneralNominalVersionedInstall232.install s e

theorem generated_root {r : Registry} {s : State roles} {root focus : Occurrence roles}
    (shape : Terminal r s root) (reaches : Generated s.core.erased.current root focus) : focus = root :=
  GeneralNominalVersionedMixedTerminalStable234.generated_only shape.raw shape.edges reaches

theorem unique_plan {r : Registry} {s : State roles} {root : Occurrence roles}
    {first last : Plan roles} (shape : Terminal r s root)
    (a : Frame r s.core root k first) (b : Frame r s.core root j last) : first = last := by
  obtain ⟨d,roster⟩ := shape.declaration
  obtain ⟨center,centers⟩ := shape.center
  apply GeneralRebaseScopedFrame276.same_frame a b
  · exact (List.mem_singleton.mp (roster ▸ a.visible)).trans (List.mem_singleton.mp (roster ▸ b.visible)).symm
  · exact (List.mem_singleton.mp (shape.raw ▸ a.raw_recorded)).trans
     (List.mem_singleton.mp (shape.raw ▸ b.raw_recorded)).symm
  · exact (List.mem_singleton.mp (centers ▸ a.center_recorded)).trans
     (List.mem_singleton.mp (centers ▸ b.center_recorded)).symm

theorem no_install {r : Registry} {s : State roles} {root : Occurrence roles}
    (shape : Terminal r s root) (held : ReadyRule r s root key children) (t : State roles) :
    ¬ InstallTransition r root s t := by
  rintro ⟨effect,reached,enabled,novel,_⟩
  obtain ⟨plan,frame,_,committed,_,_⟩ := held
  have atRoot := generated_root shape reached
  have seen := effect.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at seen
  exact novel ((unique_plan shape seen frame).symm ▸ committed)

theorem deterministic_install {r : Registry} {s : State roles} {root : Occurrence roles}
    (shape : Terminal r s root) (chosen : Effect roles) (enabled : Installable r s chosen)
    (atRoot : chosen.plan.packet.site.occurrence = root)
    (t : State roles) (action : InstallTransition r root s t) :
    t = GeneralNominalVersionedInstall232.install s chosen := by
  obtain ⟨candidate,reached,allowed,novel,rfl⟩ := action
  have rooted := generated_root shape reached
  have first := candidate.frame
  have last := chosen.frame
  rw [allowed.registry_eq,allowed.snapshot_eq,rooted] at first
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at last
  have same := unique_plan shape first last
  have registryEq : candidate.registry = chosen.registry := allowed.registry_eq.trans enabled.registry_eq.symm
  have snapshotEq : candidate.snapshot = chosen.snapshot := allowed.snapshot_eq.trans enabled.snapshot_eq.symm
  rcases candidate with ⟨a,s₁,p₁,f₁,u₁,r₁⟩
  rcases chosen with ⟨b,s₂,p₂,f₂,u₂,r₂⟩
  change a = b at registryEq
  change s₁ = s₂ at snapshotEq
  change p₁ = p₂ at same
  subst a
  subst s₁
  subst p₁
  rfl

end Yulang.GeneralRebaseTerminalAbsorb278
