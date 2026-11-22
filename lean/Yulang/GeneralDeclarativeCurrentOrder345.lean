import Yulang.GeneralDeclarativeCurrentRequest345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentOrder345
open GeneralSourceDictionaries
open GeneralNominalCenteredSteps (State)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalDemandMerging (Site)

structure Row where
  physical : Nat
  ordinal : Nat
  output : GeneralSourceState.Output

noncomputable def rows (state : State rs) (focus : Occurrence rs) : List Row := by
  classical
  exact (state.erased.current.sites.zipIdx.filter fun e =>
    Alias state.erased.current focus.identity e.1.occurrence.identity).flatMap fun entry =>
    entry.1.occurrence.demand.outputs.zipIdx.map fun out => ⟨entry.2,out.2,out.1⟩

theorem outputs (state : State rs) (focus : Occurrence rs) :
    (rows state focus).map Row.output = requests state focus := by
  classical
  unfold rows requests
  simp only [List.map_flatMap,List.map_map,Function.comp_def,List.zipIdx_map_fst]
  have filtered :
      ((state.erased.current.sites.zipIdx.filter fun e =>
        Alias state.erased.current focus.identity e.1.occurrence.identity).map Prod.fst) =
      (state.erased.current.sites.filter fun e =>
        Alias state.erased.current focus.identity e.occurrence.identity) := by
    simpa only [List.zipIdx_map_fst,Function.comp_def] using
      (List.filter_map (f := Prod.fst) (p := fun site : Site rs =>
        decide (Alias state.erased.current focus.identity site.occurrence.identity))
        (l := state.erased.current.sites.zipIdx)).symm
  simpa only [List.flatMap_map, Function.comp_def] using
    congrArg (List.flatMap fun site : Site rs => site.occurrence.demand.outputs) filtered

theorem exact_row {state : State rs} {focus : Occurrence rs} {row : Row} :
    row ∈ rows state focus ↔ ∃ site : Site rs, state.erased.current.sites[row.physical]? = some site ∧
      site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
      Alias state.erased.current focus.identity site.occurrence.identity := by
  classical
  cases row with
  | mk i j o =>
    simp only [rows,List.mem_flatMap,List.mem_filter,List.mem_map,decide_eq_true_eq]
    constructor
    · rintro ⟨⟨site,k⟩,⟨listed,alias⟩,⟨⟨out,l⟩,emitted,same⟩⟩
      cases same
      exact ⟨site,List.mk_mem_zipIdx_iff_getElem?.mp listed,List.mk_mem_zipIdx_iff_getElem?.mp emitted,alias⟩
    · rintro ⟨site,siteAt,outAt,alias⟩
      exact ⟨(site,i),⟨List.mk_mem_zipIdx_iff_getElem?.mpr siteAt,alias⟩,
        (o,j),List.mk_mem_zipIdx_iff_getElem?.mpr outAt,rfl⟩

end Yulang.GeneralDeclarativeCurrentOrder345
