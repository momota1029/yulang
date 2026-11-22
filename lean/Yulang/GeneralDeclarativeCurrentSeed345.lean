import Yulang.GeneralWhereVersionInstall317
import Yulang.GeneralNominalVersionedMixedReady235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentSeed345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepRoles (Origin Invariant origin_above)
open GeneralWhereVersionInstall317 (Journal install installCore emitted InstallStep)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadWFSource (Coverage)

theorem emitted_origin {r : Registry} {before : Journal rs} {p : Plan rs}
    (valid : Invariant (Compiled r) seed root before.mixed.core)
    (frame : Frame (Compiled r) before.mixed.core p.packet.site.occurrence p.packet.declaration.id p)
    (member : site ∈ emitted p) : Origin (Compiled r) seed root site.occurrence := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have included := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  refine Or.inr ⟨p.packet.site.occurrence.identity,p.packet.declaration,frame.visible,clause.val,included,
    origin_above (valid.raw _ frame.raw_recorded),?_,GeneralWhereVersionCompiler317.child_role _ _ _⟩
  rw [GeneralWhereVersionCompiler317.child_owner]
  change GeneralNominalIdentities.source p.packet.context.state.seed _ = _
  rw [frame.context_eq,valid.seed_eq]
  rfl

theorem after_origin {r : Registry} {before after : Journal rs} {root : Occurrence rs}
    (valid : Invariant (Compiled r) seed root before.mixed.core) (step : InstallStep r before after) :
    Invariant (Compiled r) seed root after.mixed.core := by
  cases step with
  | whereRow ctx p _ frame _ _ refinement _ _ =>
    refine ⟨?_,?_,valid.aliases,refinement.seed.trans valid.seed_eq⟩
    · intro site member
      rcases List.mem_append.mp member with old | recent
      · exact valid.raw site old
      · obtain ⟨center,added,rfl⟩ := List.mem_map.mp recent
        exact emitted_origin valid frame added
    · intro site member
      exact (List.mem_append.mp member).elim (valid.centers site) (emitted_origin valid frame)

theorem after_coverage {r : Registry} {before after : Journal rs}
    (covered : Coverage (Compiled r) before.mixed.core.erased.current.context.interpretation)
    (step : InstallStep r before after) :
    Coverage (Compiled r) after.mixed.core.erased.current.context.interpretation := by
  cases step with
  | whereRow ctx p _ _ _ _ _ same _ =>
    change Coverage (Compiled r) ctx.interpretation
    rw [same]
    exact covered

end Yulang.GeneralDeclarativeCurrentSeed345
