import Yulang.GeneralDeclarativeWitnessStopped334
import Yulang.GeneralDeclarativeWitnessFixture334

open Yulang
open GeneralDeclarativeNestedSiblingsDecl332 (registry checked)
open GeneralDeclarativeNestedSiblingsResult332 (current dictionary)
open GeneralDeclarativeNestedSiblingsFrame332 (final covered wanted_root)
open GeneralDeclarativeNestedSiblingsModels332 (inhabited)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeWitnessFixture334
open GeneralDeclarativeWitnessStopped334
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Summarizes)

example (done : Nat → Prop) :
    ∃ tree, Retained (current done) registry interpretation waiting root tree ∧
      Summarizes tree (.selected dictionary) :=
  (selected_iff_retained checked covered wanted_root).mp (actual_tree done)

example (done : Nat → Prop) :
    ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨tree,kept,summary⟩ := (selected_iff_retained checked covered wanted_root).mp (actual_tree done)
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨m,fit,(selected_receipt checked covered wanted_root kept summary).2 _ fit⟩

#print axioms Yulang.GeneralDeclarativeWitnessStopped334.same_key_of_visible
#print axioms Yulang.GeneralDeclarativeWitnessStopped334.resolves
#print axioms Yulang.GeneralDeclarativeWitnessStopped334.selected_receipt
#print axioms Yulang.GeneralDeclarativeWitnessStopped334.retain_selected
#print axioms Yulang.GeneralDeclarativeWitnessStopped334.selected_iff_retained
