import Yulang.GeneralRebaseMergeJournal269
import Yulang.GeneralRebaseNonpointK2Fixture269
import Yulang.GeneralNominalProgressObstruction

namespace Yulang.GeneralRebaseNonliteralMergeFixture269
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site SameInputs rootSite)
open GeneralNominalVersionedJournal232 (Models initial)
open GeneralRebaseNonpointK2Fixture269 (source witnessed)
open GeneralNominalProgressObstruction (model)
open CommonNominalFullCarrier

abbrev root (name input : Nat) : Occurrence roles :=
 ⟨name,⟨0,fun _ => (input,input),[],by intro _ bad; cases bad⟩⟩

abbrev context : GeneralNominalCandidates.Context := ⟨source,GeneralNominalExamples.interpretation⟩
abbrev journal := initial context (root 40 0)
abbrev first : Site roles := rootSite source.seed (root 40 0)
abbrev last : Site roles := rootSite source.seed (root 41 1)

theorem witnessed_journal : Models journal model := by
 apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
 exact ⟨witnessed,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

theorem not_literal :
 GeneralRebaseMergeCenters267.same first last = false := by decide +kernel

theorem calculated :
 GeneralRebaseSameInputs269.probe journal (fun _ _ => none) first last = some true := by decide +kernel

/-- Two distinct literal center names compare equal in all models of this
initialized journal, without a supplied equality bit. The comparison site
is not asserted registered and no actual merge step is inferred here. -/
theorem same_nonliteral : SameInputs (Models journal) first last := by
 have h := GeneralRebaseSameInputs269.probe_sound journal (fun _ _ => none) (fun _ _ => True.intro) first last
 rw [calculated] at h
 exact h

end Yulang.GeneralRebaseNonliteralMergeFixture269
