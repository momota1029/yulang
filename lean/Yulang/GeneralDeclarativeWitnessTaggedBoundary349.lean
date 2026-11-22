import Yulang.GeneralDeclarativeWitnessExactProjection349
import Yulang.GeneralDeclarativeTaggedDictionary340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTaggedBoundary349
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessHeader349 (replay replay_sound)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support)
open GeneralDeclarativeWitnessExactRest349 (Wire)
open GeneralDeclarativeWitnessExactProjection349 (checkedList fixed_models)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report classifies)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeTaggedDictionary340 (Rule dictionary_sound)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Tree Dictionary Resolves Classify)

/-- The finite header and compiled projection receipts now discharge
the registry and exact-sidecar obligations without enlarging the
current state. Checking the tagged local choices and recursive ordered
tree is separate and explicit in `choices`; the solver's own result
is not a source of that derivation. -/
theorem sound_given_replayed_tree {p : Problem} {manifest : Manifest}
    {a : Attached p.state manifest} {metadata : SourceBundle} {report : Report}
    {es : List Entry} {codes : List Wire} {tree : Tree} {result : Dictionary}
    {waiting : Demand → Declaration → Prop}
    (header : replay p ⟨report.outputs⟩ = some metadata)
    (same : agrees p tree report = true)
    (selected : report.result = .selected result)
    (proofs : checkedList p.state es codes = true)
    (choices : Resolves (Rule (support a) es (registry metadata)
      (interpretation metadata.snapshot) waiting) p.demand tree) :
    report.tree = tree ∧ report.outputs = p.demand.outputs ∧
      Classify (Rule (support a) es (registry metadata) (interpretation metadata.snapshot) waiting)
        p.demand (.selected result) ∧
      ∀ m : Assignment, Models p.state m →
        Evidence (registry metadata) (interpretation metadata.snapshot) m p.demand result := by
  have matched := exact_report same
  have choice := classifies choices same
  rw [selected] at choice
  obtain ⟨_,catalogue,cover,declares,_⟩ := replay_sound header
  exact ⟨matched.1,matched.2.2,choice,fun m mOk =>
    dictionary_sound catalogue cover declares choice (fixed_models proofs m mOk)⟩

end Yulang.GeneralDeclarativeWitnessTaggedBoundary349
