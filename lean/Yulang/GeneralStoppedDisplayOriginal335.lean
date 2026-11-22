import Yulang.GeneralStoppedDisplayExtendedChoice335
import Yulang.GeneralDeclarativeWitnessStopped334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralStoppedDisplayOriginal335
open GeneralStoppedDisplayProjection335
open GeneralStoppedDisplayExtended335
open GeneralStoppedDisplayExtendedChoice335
open GeneralStoppedDisplayCut335 (sourceSpans protect fallback targets reminted closed)
open GeneralStoppedDisplayGuard335 (waiting covered list_trace list_print int_print parent_declared)
open GeneralNominalExamples (registry interpretation intDisplay registry_checked)
open GeneralDeclarationExamples (display)
open GeneralRebaseDisplayExecutor276 (run raw run_exact)
open GeneralDeclarativeWitnessHead334 (Slice full)
open GeneralDeclarativeWitnessNode334 (Witness)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeWitnessStopped334 (Retained selected_iff_retained)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralStoppedPlacement335 (SameDemand)
open CommonRoleOutermostResolver (Classify Summarizes Tree)

noncomputable def rootSlice (done : Nat → Prop) : Slice (augmented done) :=
  ⟨ordinary,supported done,contains_raw,same_read_rows⟩

noncomputable def rootWitness (done : Nat → Prop) :
    Witness (augmented done) registry interpretation waiting parentDemand display [reminted] where
  chosen := elect_parent done
  slice := rootSlice done
  protect := protect
  fallback := fallback
  targets := targets
  named := ordinary
  spans := sourceSpans
  source := .cons (.named ⟨point_bounded _ _,_,_,list_print,list_trace done .actual,
    .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil⟩) .nil
  ordinary := expanded
  compiled := written
  receipt := literal (reflexive _)

def childWitness (done : Nat → Prop) :
    Witness (augmented done) registry interpretation waiting reminted intDisplay [] where
  chosen := elect_child done
  slice := full (augmented done)
  protect := protect
  fallback := fallback
  targets := targets
  named := expanded
  spans := []
  source := .cons (.named ⟨child_bounds,_,_,int_print,scalar_from (alias_refl _) .actual,.nil⟩) .nil
  ordinary := expanded
  compiled := child_compiles
  receipt := literal (reflexive _)

theorem exact_original_dictionary (done : Nat → Prop) :
    Classify (Rule (augmented done) registry interpretation waiting) parentDemand (.selected (.node 1 [.node 3 []])) :=
  ⟨.selected 1 [.selected 3 []],
    .selected (.selected (rootWitness done)) (.cons (.selected (.selected (childWitness done)) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem finite_replayed (done : Nat → Prop) :
    ∃ tree, Retained (augmented done) registry interpretation waiting parentDemand tree ∧
      Summarizes tree (.selected (.node 1 [.node 3 []])) :=
  (selected_iff_retained registry_checked covered parent_declared).mp (exact_original_dictionary done)

/-- The active I-60 compiler can be retained for the actual stopped
raw case, provided representation transport is explicit. The ordinary
child is the exact compiler output at its distinct endpoint names.
Only the previously existing raw names receive same-assignment
guarantees; fresh logical endpoints are constrained in the extension. -/
theorem actual_success (done : Nat → Prop) (finished : run key = some (phase,payload)) :
    Classify (Rule (augmented done) registry interpretation waiting) parentDemand (.selected payload) ∧
    SameDemand expanded childDemand reminted ∧
    ∀ m, GeneralNominalVersionedJournal232.Models (raw phase) m →
      ∃ n, Models expanded n ∧ (∀ name ∈ stateNames closed, n name = m name) ∧
        GeneralNominalVersionedJournal232.Models (raw phase) n ∧
        Evidence registry interpretation n parentDemand payload := by
  obtain ⟨_,rfl,rfl⟩ := (run_exact key phase payload).mp finished
  have seen := exact_original_dictionary done
  refine ⟨seen,placement,?_⟩
  intro m fit
  obtain ⟨n,ordinary,kept⟩ := (conservative m).mp fit
  exact ⟨n,ordinary,kept,(conservative n).mpr ⟨n,ordinary,fun _ _ => rfl⟩,
    dictionary_sound registry_checked covered parent_declared seen n ordinary⟩

end Yulang.GeneralStoppedDisplayOriginal335
