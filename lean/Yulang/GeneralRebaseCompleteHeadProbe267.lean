import Yulang.GeneralRebaseInstallCandidates267

namespace Yulang.GeneralRebaseCompleteHeadProbe267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Honest atFocus positive unresolved observation)
open GeneralRebaseSourceClassification267 (verdict)
open GeneralRebasePartialClassification267 (Verdict)

def Covered (probe : Plan roles → Option Bool) (entries : List (Plan roles)) : Prop :=
 ∀ plan ∈ entries, probe plan ≠ none

theorem unresolved_empty (probe : Plan roles → Option Bool) (entries : List (Plan roles))
 (complete : Covered probe entries) : unresolved probe entries = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro plan inside
 obtain ⟨member,unknown⟩ := (GeneralRebaseHeadProbe267.unresolved_exact ..).mp inside
 exact complete plan member unknown

theorem unique_from_complete (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (complete : Covered probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (unique : Unique (Encoded registry) state.core.erased.current.context focus key kids) :
 verdict probe (atFocus (Encoded registry) state root focus (declChecked checked)) = .unique (key,kids) := by
 let entries := atFocus (Encoded registry) state root focus (declChecked checked)
 have empty := unresolved_empty probe entries complete
 have member : (key,kids) ∈ positive probe entries := by
   rcases GeneralRebaseHeadProbe267.source_complete_or_unknown registry state root focus checked reachable
      generated probe honest unique.1 with yes | ⟨plan,unknown,_⟩
   · exact yes
   · exact False.elim (complete plan ((GeneralRebaseHeadProbe267.unresolved_exact ..).mp unknown).1
       ((GeneralRebaseHeadProbe267.unresolved_exact ..).mp unknown).2)
 have every (entry : GeneralRebaseHeadProbe267.Match roles) (listed : entry ∈ positive probe entries) : entry = (key,kids) := by
   rcases entry with ⟨k,children⟩
   have real := GeneralRebaseHeadProbe267.source_sound registry state root focus checked metadata probe honest listed
   obtain ⟨sameKey,sameKids⟩ := unique.2 k children real
   exact Prod.ext sameKey sameKids
 letI : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq
 change GeneralRebasePartialClassification267.classify (positive probe entries) ((unresolved probe entries).map observation) = _
 rw [empty]
 cases literal : positive probe entries with
 | nil => simp [literal] at member
 | cons first rest =>
   have same := every first (literal.symm ▸ List.mem_cons_self)
   subst first
   exact GeneralRebasePartialClassification267.unique_despite_duplicate_unknown (key,kids) rest []
      (fun entry seen => every entry (literal.symm ▸ List.mem_cons_of_mem _ seen)) (by simp)

end Yulang.GeneralRebaseCompleteHeadProbe267
