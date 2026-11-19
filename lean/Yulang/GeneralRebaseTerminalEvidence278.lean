import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralRebaseRoundMicro278

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTerminalEvidence278
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231 (Evidence Instance Frame)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralNominalCenteredHeadOutputs (requests)
variable {roles : Roles.RoleDecls}

theorem no_class_requests {s : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
    (empty : requests s root = []) (p : Plan roles) (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects s root p m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor <;> intro output member
  · rw [empty] at member
    cases member
  · rw [empty] at member
    cases member

theorem effect_leaf (e : Effect roles) (m : Assignment) (held : Holds e.plan m)
    (empty : requests e.snapshot e.plan.packet.site.occurrence = [])
    (terminal : GeneralNominalVersionedFrame231.children e.plan.packet = []) :
    Evidence e.registry e.snapshot m e.plan.packet.site.occurrence (.node e.plan.packet.declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf
    ⟨e.plan,GeneralNominalVersionedEvidence231.certificate_of_semantics e.frame terminal.symm
      held e.ready (no_class_requests empty e.plan m)⟩

theorem no_children (p : Plan roles) (terminal : p.packet.declaration.requirements = []) :
    GeneralNominalVersionedFrame231.children p.packet = [] := by
  apply List.length_eq_zero_iff.mp
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences p,List.length_map,
    GeneralNominalVersionedChildren232.emitted_length,terminal]
  rfl

theorem leaf_shape {reg : Registry} {s : GeneralNominalCenteredSteps.State roles}
    {root : Occurrence roles} {m : Assignment} {d : Declaration} {data : Payload}
    (one : reg.declarations = [d]) (terminal : d.requirements = [])
    (evidence : Evidence reg s m root data) : data = .node d.id [] := by
  have checked := (payload_iff_erased _ _ _).mpr evidence
  cases checked with
  | node instanceRule all =>
    obtain ⟨p,checked⟩ := instanceRule
    have same : p.packet.declaration = d := List.mem_singleton.mp (one ▸ checked.frame.visible)
    have empty := no_children p (same.symm ▸ terminal)
    rw [checked.children_eq,empty] at all
    cases all
    rw [← checked.frame.key_eq,same]

end Yulang.GeneralRebaseTerminalEvidence278
