import Yulang.GeneralVersionedForwardedWrites312
import Yulang.GeneralVersionedBinderReuse312
import Yulang.GeneralVersionedSemanticPeer312

set_option backward.isDefEq.respectTransparency false
/-! A nonleaf family without prospective internal write premises. Forwarding
can contain ordered/repeated child clauses and output-only named requests.
Selection and actual child evidence remain distinct operational facts. -/
namespace Yulang.GeneralVersionedForwardedJoint312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralNominalSaturationState (Alias)
open GeneralVersionedForwardedWrites312 (Forwarded)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles}
  {root : Occurrence roles} {children : List (Occurrence roles)} {e : Effect roles} {past : Plan roles}

theorem joint
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry)
    (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (history : past ∈ s.plans)
    (alias : Alias s.core.erased.current e.plan.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (declaration : e.plan.packet.declaration = past.packet.declaration)
    (support : Support s names) (sites : Covered s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s e.plan) s e.plan.packet)
    (owned : GeneralVersionedBinderReuse312.Owned s e.plan names)
    (forwarded : Forwarded e.plan.packet.declaration) : ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  exact GeneralVersionedHistoricalJoint312.joint checked path pick registryEq snapshot history alias declaration
    inhabited support sites ledger
    (GeneralVersionedBinderReuse312.head_table checked path frame history alias declaration owned)
    (GeneralVersionedForwardedWrites312.internal s e forwarded)

theorem installable
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry)
    (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m)
    (history : past ∈ s.plans)
    (alias : Alias s.core.erased.current e.plan.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (support : Support s names) (sites : Covered s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s e.plan) s e.plan.packet)
    (owned : GeneralVersionedBinderReuse312.Owned s e.plan names)
    (forwarded : Forwarded e.plan.packet.declaration)
    (coverage : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current e.plan.packet.site.occurrence.identity prior.site.occurrence.identity →
      GeneralVersionedSemanticPeer312.Coverage registry s e.plan.packet.site.occurrence prior.declaration) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e := by
  have compatible := GeneralVersionedSemanticPeer312.choice checked path pick inhabited coverage
  have seen : past.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable path).2]
    exact List.mem_map.mpr ⟨past,history,rfl⟩
  have current := registryEq ▸ e.frame.visible
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _ current
    (GeneralNominalVersionedMixedChoiceHistory236.visible path seen) (compatible past.packet seen alias)
  exact (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked path pick registryEq snapshot).mpr
    ⟨compatible,joint checked path pick registryEq snapshot inhabited history alias declaration support sites ledger owned forwarded⟩

theorem evidence_node
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry)
    (snapshot : e.snapshot = s.core)
    (stable : (boundary roles).Stable registry s e.plan.packet.site.occurrence)
    (origin : e.plan.packet.site.occurrence = root ∨
      GeneralNominalSaturationState.Generated s.core.erased.current root e.plan.packet.site.occurrence)
    (history : past ∈ s.plans)
    (alias : Alias s.core.erased.current e.plan.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (support : Support s names) (sites : Covered s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s e.plan) s e.plan.packet)
    (owned : GeneralVersionedBinderReuse312.Owned s e.plan names)
    (forwarded : Forwarded e.plan.packet.declaration)
    (coverage : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current e.plan.packet.site.occurrence.identity prior.site.occurrence.identity →
      GeneralVersionedSemanticPeer312.Coverage registry s e.plan.packet.site.occurrence prior.declaration)
    (valid : Models s model)
    (actual : CommonRoleOutermostResolver.All₂
      (GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core model) children dictionaries) :
    GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core model
      e.plan.packet.site.occurrence (.node e.plan.packet.declaration.id dictionaries) ∧
    ∀ child ∈ children, GeneralNominalSaturationState.Generated s.core.erased.current root child := by
  have enabled := installable checked path pick registryEq snapshot ⟨model,valid⟩ history alias support sites
    ledger owned forwarded coverage
  have selected := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp pick
  exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled rfl selected valid actual,
    fun _ present => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled rfl
      selected origin present⟩

end Yulang.GeneralVersionedForwardedJoint312
