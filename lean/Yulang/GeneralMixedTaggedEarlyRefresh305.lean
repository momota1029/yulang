import Yulang.GeneralMixedScalarPartial305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralMixedTaggedEarlyRefresh305
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (old target from_source present previously_unknown)
open GeneralNominalCatalogueExtension305 (extend equivalent)
open GeneralNominalReportContext305 (EquivalentContexts model_iff)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedScalarPartial305 (partialContext still_known seen_known unseen_unknown after_known full_known)
open GeneralMixedReindexOutputFixture305 (wide widened coordinates)
open GeneralMixedReindexOutputHalt305 (widened_halted)
open GeneralMixedRawFanout305 (firstTag firstTag_widened bounded_tags)
open GeneralRebaseDepthPathRank285 (ActualPath)

noncomputable def tagged (which : Fin 2) (tag : Nat) : GeneralNominalCandidates.Context :=
  ⟨extend (partialContext which).state (.variant tag) (by trivial) (fun i => Fin.elim0 i),
    old.interpretation⟩

noncomputable def tagged_iso (which : Fin 2) (tag : Nat) :
    EquivalentContexts (partialContext which) (tagged which tag) :=
  equivalent (partialContext which) (.variant tag) (by trivial) (fun i => Fin.elim0 i)

noncomputable def firstCert (which : Fin 2) (tag : Nat) : Refresh installed (tagged which tag) := by
  let oldR := GeneralNominalRefinements.refl old.state
  refine ⟨⟨oldR.base,oldR.heads,oldR.nominals,oldR.ordinary,
    fun id was => (tagged_iso which tag).forward.known id (still_known which id was),
    oldR.reserved,oldR.allocated,rfl,rfl⟩,rfl,(fun _ held => held),
    (fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩),?_⟩
  intro observation recorded
  exact ⟨[],[],.source,.source,fun m _ valid =>
    GeneralCanonicalObservations.recorded_sound (tagged which tag).state m
      ((model_iff (tagged_iso which tag) m).mp (from_source m valid.1)) recorded⟩

noncomputable def middle (which : Fin 2) (tag : Nat) : State roles :=
  refresh installed (tagged which tag)

theorem first_actual (which : Fin 2) (tag : Nat) : Step registry root installed (middle which tag) :=
  ⟨root,.root,.refresh root (tagged which tag) (firstCert which tag) which.val
    (present which.val (Nat.le_of_lt_succ which.isLt))
    (previously_unknown which.val (Nat.le_of_lt_succ which.isLt))
    ((tagged_iso which tag).forward.known _ (seen_known which))⟩

noncomputable def finishCert (which : Fin 2) (tag finish : Nat) :
    Refresh (middle which tag) (wide finish) := by
  let oldR := GeneralNominalRefinements.refl old.state
  refine ⟨⟨oldR.base,oldR.heads,oldR.nominals,oldR.ordinary,?_,
    oldR.reserved,oldR.allocated,rfl,rfl⟩,rfl,(fun _ held => held),
    (fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩),?_⟩
  · exact fun id yes => (coordinates finish).forward.known id
      (after_known which id ((tagged_iso which tag).backward.known id yes))
  · intro observation recorded
    exact ⟨[],[],.source,.source,fun m _ valid =>
      GeneralCanonicalObservations.recorded_sound (wide finish).state m
        ((model_iff (coordinates finish) m).mp (from_source m valid.1)) recorded⟩

theorem second_actual (which other : Fin 2) (different : which ≠ other) (tag finish : Nat) :
    Step registry root (middle which tag) (widened finish) :=
  ⟨root,.root,.refresh root (wide finish) (finishCert which tag finish) other.val
    (present other.val (Nat.le_of_lt_succ other.isLt))
    (fun promoted => unseen_unknown which other different ((tagged_iso which tag).backward.known _ promoted))
    ((coordinates finish).forward.known _ (full_known other))⟩

theorem both_orders_arbitrary_labels (which : Fin 2) (tag finish : Nat) :
    ActualPath installed (widened finish) 2 :=
  .more (.more (.empty _) (first_actual which tag))
    (second_actual which which.rev (by
      intro same
      have numbers := congrArg Fin.val same
      rw [Fin.val_rev] at numbers
      have bound := which.isLt
      omega) tag finish)

theorem middle_label (which : Fin 2) (tag : Nat) : firstTag (middle which tag) = tag := rfl

/-- Fix a single fully checked endpoint. No finite list of raw intermediate
states covers the two-refresh schedules to that very endpoint, for either
choice of which scalar becomes known first. This is not an infinite path. -/
theorem arbitrary_early_fanout (which : Fin 2) (finish : Nat) (listed : List (State roles)) :
    ∃ mid, mid ∉ listed ∧ Step registry root installed mid ∧
      Step registry root mid (widened finish) := by
  let tags := listed.map firstTag
  let n := tags.foldr Nat.max 0 + 1
  refine ⟨middle which n,?_,first_actual which n,second_actual which which.rev ?_ n finish⟩
  · intro member
    have memory : n ∈ tags := by
      change n ∈ listed.map firstTag
      rw [← middle_label which n]
      exact List.mem_map_of_mem member
    exact Nat.not_succ_le_self _ (bounded_tags memory)
  · intro same
    have numbers := congrArg Fin.val same
    rw [Fin.val_rev] at numbers
    have bound := which.isLt
    omega

end Yulang.GeneralMixedTaggedEarlyRefresh305
