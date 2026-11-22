import Yulang.GeneralDeclarativeWhereStore346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereStoreReplay346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralWhereOriginConfig318 (Config)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionCompiler317 (schema)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhereReuse346 (SameAuthor same_author)
open GeneralDeclarativeWhereStore346 (Store exact_before_lookup)

theorem replay {j : Journal rs} {p : Plan rs} (checked : (boundary rs).Checked r)
    (track : Store r j) (frame : Frame (Compiled r) j.mixed.core focus tag p)
    (c : Cell p) {i : Fin (rawOf j).base.slots}
    (hit : sourceSlot (rawOf j).base c.row.target = some i) (m : Assignment) (valid : Models j m) :
    ∃ (k : Nat) (prior : Plan rs) (d : Cell prior), j.versionedWhere[k]? = some prior ∧
      d.row.target = c.row.target ∧ d.row ∈ (schema prior).equations ∧ SameAuthor c d ∧
      d.row.Holds (variables prior m) m ∧ c.row.Holds (variables p m) m := by
  have atSeed : (rawOf j).seed = p.packet.context.state.seed :=
    congrArg (fun ctx : Context => ctx.state.seed) frame.context_eq.symm
  obtain ⟨prior,d,k,stamp,eq⟩ := exact_before_lookup track hit (c.high atSeed)
  have inPast : prior ∈ j.versionedWhere := List.mem_iff_getElem?.mpr ⟨_,stamp⟩
  have config := track.drawing prior inPast
  have registry := frame.registry_eq.trans config.registry.symm
  have interpretation := (congrArg Context.interpretation frame.context_eq).trans config.interp.symm
  have seed := atSeed.symm.trans config.seed.symm
  have checkedP : GeneralDeclarations.Checked p.packet.registry :=
    frame.registry_eq.symm ▸ (checked_compiled checked).2
  have current : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq.symm ▸ frame.visible
  have oldVisible : prior.packet.declaration ∈ prior.packet.registry.declarations := config.registry.symm ▸ config.visible
  have older := (valid.2 prior inPast).1.rows _ d.written.1
  have fresh := (GeneralWhereVersionStoredRow317.same_target_iff checkedP registry interpretation seed
    current oldVisible c.written.2 d.written.2 eq.symm m).mpr older
  exact ⟨k,prior,d,stamp,eq,d.written.1,same_author c d checkedP registry interpretation seed current oldVisible eq.symm,
    older,fresh⟩

end Yulang.GeneralDeclarativeWhereStoreReplay346
