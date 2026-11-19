import Yulang.GeneralRebasePartialClassification267

namespace Yulang.GeneralRebaseSourceClassification267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Match Honest observation atFocus positive unresolved source_sound source_complete_or_unknown)
open GeneralRebasePartialClassification267 (Verdict classify classify_valid Valid)

def verdict (probe : Plan roles → Option Bool) (entries : List (Plan roles)) : Verdict (Match roles) :=
 letI : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq
 classify (positive probe entries) ((unresolved probe entries).map observation)

theorem structural_valid (probe : Plan roles → Option Bool) (entries : List (Plan roles)) :
 Valid (positive probe entries) ((unresolved probe entries).map observation) (verdict probe entries) := by
 unfold verdict
 apply classify_valid

/-- This is the independent survivor layer; a no-survivor conclusion alone
does not establish source-language rejection. -/
def Justified (registry : Registry) (state : State roles) (focus : Occurrence roles) :
 Verdict (Match roles) → Prop
 | .none => ∀ key kids, ¬ Survivor registry state.core.erased.current.context focus key kids
 | .unique (key,kids) => Unique registry state.core.erased.current.context focus key kids
 | .ambiguous (first,one) (last,two) => first ≠ last ∧
   Survivor registry state.core.erased.current.context focus first one ∧
   Survivor registry state.core.erased.current.context focus last two
 | .deferred => True

theorem source_valid (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked))) :
 Justified (Encoded registry) state focus
   (verdict probe (atFocus (Encoded registry) state root focus (declChecked checked))) := by
 let entries := atFocus (Encoded registry) state root focus (declChecked checked)
 have sound {key kids} (seen : (key,kids) ∈ positive probe entries) :
   Survivor (Encoded registry) state.core.erased.current.context focus key kids :=
   source_sound registry state root focus checked metadata probe honest seen
 have cover {key kids} (actual : Survivor (Encoded registry) state.core.erased.current.context focus key kids) :
   (key,kids) ∈ positive probe entries ∨ (key,kids) ∈ (unresolved probe entries).map observation := by
   rcases source_complete_or_unknown registry state root focus checked reachable generated probe honest actual with yes | possible
   · exact Or.inl yes
   · exact Or.inr (List.mem_map.mpr possible)
 change Justified (Encoded registry) state focus (verdict probe entries)
 have valid := structural_valid probe entries
 cases result : verdict probe entries with
 | none =>
   rw [result] at valid
   obtain ⟨knownEmpty,possibleEmpty⟩ := valid
   intro key kids actual
   have one := cover actual
   simp only [knownEmpty,possibleEmpty,List.not_mem_nil,or_self] at one
 | unique item =>
   rcases item with ⟨key,kids⟩
   rw [result] at valid
   obtain ⟨known,allKnown,allPossible⟩ := valid
   refine ⟨sound known,fun other otherKids actual => ?_⟩
   have equal : (other,otherKids) = (key,kids) := (cover actual).elim
     (allKnown (other,otherKids)) (allPossible (other,otherKids))
   exact Prod.mk.inj equal
 | ambiguous a b =>
   rcases a with ⟨first,one⟩
   rcases b with ⟨last,two⟩
   rw [result] at valid
   obtain ⟨oneSeen,twoSeen,diff⟩ := valid
   have oneReal := sound oneSeen
   have twoReal := sound twoSeen
   refine ⟨?_,oneReal,twoReal⟩
   intro same
   subst last
   have childrenSame := GeneralNominalVersionedCandidates231.survivor_children_functional
     (GeneralNominalCenteredHeadAllocEncoding.registry_checked checked.2) oneReal twoReal
   exact diff (Prod.ext rfl childrenSame)
 | deferred => trivial

end Yulang.GeneralRebaseSourceClassification267
