import Yulang.GeneralMixedCompoundHalfView307
import Yulang.GeneralMixedCompoundRefreshBound307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundHalfRun307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundRefresh239 (refreshed certificate)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot extendedContext)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundHalfView307 (snap context half)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperRefresh307 (upperState cert)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalRefinements (Refines)
open GeneralNominalState (Known sources)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralMixedCompoundRefreshBound307 (Run)

theorem high : 4 < hi := GeneralNominalIdentities.source_above_seed snapshot.seed _

theorem high_absent : ¬ Known point.core.erased.current.context.state hi := by
  intro known
  obtain ⟨slot,eq,_⟩ := known
  have bound := slot.isLt
  change slot.val < 5 at bound
  change slot.val = hi at eq
  have h := high
  omega

noncomputable def halfRefines : Refines point.core.erased.current.context.state snap := by
  let prior :=  certificate.refines
  refine ⟨prior.base,prior.heads,prior.nominals,prior.ordinary,?_,
    prior.reserved,prior.allocated,prior.seed,prior.constructors⟩
  intro n known
  exact GeneralMixedCompoundHalfView307.old_known (prior.known n known) (fun h => high_absent (h ▸ known))

noncomputable def first : Refresh point context :=
  ⟨halfRefines,certificate.interpretation,certificate.support,certificate.constraints,fun fact found =>
    certificate.cache fact (GeneralMixedCompoundHalfView307.observed_back fact found)⟩

theorem alias_forward (al : GeneralNominalSaturationState.Alias point.core.erased.current a b) :
    GeneralNominalSaturationState.Alias half.core.erased.current a b := by
  induction al with
  | refl => exact .refl _
  | edge mem => exact .edge mem
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

theorem settled_forward (h : GeneralNominalSupport.Discharged point.core.erased.current focus) :
    GeneralNominalSupport.Discharged half.core.erased.current focus := by
  induction h with
  | packet p mem _ ih => exact .packet p mem ih
  | alias a b one two same _ ih => exact .alias a b one two (alias_forward same) ih

theorem discharged_forward (h : GeneralNominalVersionedSupport233.Discharged point focus) :
    GeneralNominalVersionedSupport233.Discharged half focus := by
  induction h with
  | packet p mem _ ih => exact .packet p mem ih
  | alias a b one two same _ ih => exact .alias a b one two (alias_forward same) ih

theorem legacy_forward {facts} (previous : GeneralNominalCenteredHeadMatStepSupport.Trusted point.legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Trusted half.legacy facts := by
  induction previous with
  | source => exact .source
  | input p _ one read ih => exact .input p ih one read
  | output effect _ one plan within read stable ih =>
    exact .output effect ih one plan within read
      ⟨stable.1,fun d h => settled_forward (stable.2 d h)⟩
  | merge a b _ one two al all witnessed same ih =>
    exact .merge a b ih one two (alias_forward al) all witnessed same

theorem versioned_forward {facts} (previous : GeneralNominalVersionedSupport233.Trusted point facts) :
    GeneralNominalVersionedSupport233.Trusted half facts := by
  induction previous with
  | source => exact .source
  | input p _ mem read ih => exact .input p ih mem read
  | output e _ mem keep input read settled ih =>
    exact .output e ih mem keep input read
      ⟨settled.1,fun d h => discharged_forward (settled.2 d h)⟩
  | merge a b _ one two al all witnessed same ih =>
    exact .merge a b ih one two (alias_forward al) all witnessed same

theorem cached : CacheSound half extendedSnapshot := by
  intro item seen
  obtain ⟨older,newer,oldTrust,newTrust,sound⟩ := certificate.cache item seen
  exact ⟨older,newer,legacy_forward oldTrust,versioned_forward newTrust,sound⟩

noncomputable def second : Refresh half extendedContext := by
  let self := GeneralNominalRefinements.refl extendedSnapshot
  refine ⟨⟨self.base,self.heads,self.nominals,self.ordinary,
    fun _ h => GeneralMixedCompoundHalfView307.forward_known h,
    self.reserved,self.allocated,self.seed,self.constructors⟩,
    rfl,(fun _ yes => yes),(fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩),cached⟩

theorem half_run : Run 1 half :=
  .more .zero context first lo (GeneralDictionaryCompoundRefresh239.supported 5 (by decide))
    GeneralDictionaryCompoundRefreshStep239.lower_unknown GeneralMixedCompoundHalfView307.lo_known

theorem hi_supported : hi ∈ sources snap :=
  GeneralNominalAllocationSupport.slot_source snap (6 : Fin 7)

theorem step_by_two : Run 2 refreshed :=
  .more half_run extendedContext second hi hi_supported
    GeneralMixedCompoundHalfView307.hi_unknown GeneralMixedCompoundHalfView307.hi_known

theorem by_three : Run 3 upperState :=
  .more step_by_two GeneralMixedCompoundUpperSnapshot307.context cert upper
    GeneralMixedCompoundUpperSnapshot307.upper_supported GeneralMixedCompoundUpperSnapshot307.upper_unknown
    GeneralMixedCompoundUpperSnapshot307.upper_known

theorem by_two : Run 2 upperState :=
  .more (.more .zero extendedContext certificate lo (GeneralDictionaryCompoundRefresh239.supported 5 (by decide))
    GeneralDictionaryCompoundRefreshStep239.lower_unknown GeneralDictionaryCompoundRefreshStep239.lower_known)
    GeneralMixedCompoundUpperSnapshot307.context cert upper GeneralMixedCompoundUpperSnapshot307.upper_supported
    GeneralMixedCompoundUpperSnapshot307.upper_unknown GeneralMixedCompoundUpperSnapshot307.upper_known

theorem sharp : (∀ n s, Run n s → n ≤ 3) ∧ Run 3 upperState ∧ Run 2 upperState :=
  ⟨fun _ _ => GeneralMixedCompoundRefreshBound307.bound,by_three,by_two⟩

end Yulang.GeneralMixedCompoundHalfRun307
