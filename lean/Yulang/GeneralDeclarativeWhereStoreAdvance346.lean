import Yulang.GeneralDeclarativeWhereStoreReplay346
import Yulang.GeneralDeclarativeWherePhysical346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereStoreAdvance346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal InstallStep install)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell High Delta)
open GeneralWhereOriginConfig318 (Config step_config fresh_record_context)
open GeneralDeclarativeWhereStore346 (Store)
open GeneralNominalIdentities (source)

theorem under_install {j : Journal rs} {p : Plan rs} {ctx : Context}
    (track : Store r j) (delta : Delta (rawOf j) ctx.state p)
    (step : InstallStep r j (install j ctx p)) : Store r (install j ctx p) := by
  constructor
  · intro i high
    change High ctx.state (ctx.state.base.source i) at high
    rcases delta.split_slot i high with ⟨prior,eq⟩|⟨fresh,member,eq⟩
    · have named : High (rawOf j) ((rawOf j).base.source prior) := by
        obtain ⟨key,tag,address⟩ := high
        exact ⟨key,tag,eq.symm.trans (address.trans (by rw [delta.refinement.seed]))⟩
      obtain ⟨owner,recorded,cell,same⟩ := track.owned prior named
      exact ⟨owner,List.mem_append_left _ recorded,cell,same.trans eq.symm⟩
    · exact ⟨p,List.mem_append_right _ List.mem_cons_self,fresh,eq.symm⟩
  · intro q member
    have info := step_config step
    by_cases past : q ∈ j.versionedWhere
    · obtain ⟨registry,visible,interp,seed⟩ := track.drawing q past
      exact ⟨registry,visible,interp.trans info.1.symm,seed.trans delta.refinement.seed.symm⟩
    · have source := (info.2 q member).resolve_left past
      have ctxEq := fresh_record_context step q member past
      exact ⟨source.1,source.2,(congrArg Context.interpretation ctxEq).trans info.1.symm,
        (congrArg (fun a : Context => a.state.seed) ctxEq).trans delta.refinement.seed.symm⟩

end Yulang.GeneralDeclarativeWhereStoreAdvance346
