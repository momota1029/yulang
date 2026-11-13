import Yulang.GeneralNominalBranchingCaptures
import Yulang.GeneralPatternGroundSubstitution

/-! Simultaneous finite values are selected from actual captured projections.
Every repeated use receives the same per-name value through shared origins. -/
namespace Yulang.GeneralNominalBranchingLabels
open GeneralNominalRecursiveInspection GeneralNominalBranchingReadback
open GeneralNominalBranchingCaptures GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalSharedCaptures
open GeneralNominalSaturationState GeneralNominalStructuralContainment
open GeneralPatternGroundSubstitution CommonNominalFullCarrier

theorem path_unique {model : GeneralNominalCommonBridge.Assignment}
    (path : Path root depth origin) (initial : Unique model root) : Unique model origin := by
  induction path with
  | root => exact initial
  | nominal prior ih =>
    intro a b one two
    cases one with
    | nominal first head found =>
      cases two with
      | nominal last other located =>
        have equal := ih _ _ first last
        exact ((nominal_regular_invariant_exact ..).mp
          (subtype_trans head.2 (subtype_trans equal.1 other.1))).2.2 _ _ _ found located
  | pair index prior ih =>
    exact projection_unique ih (.structural .pair) trivial index

theorem captured_tree (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds model)
    (queries : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = [query])
    (shape : QueryShape query) (recorded : packet.site.inputs[0]? = some (some origin))
    (tree : Tree) (meaning : At model .actual origin tree.value)
    (usable : Usable packet name actual) :
    ∃ part : Tree, part.mass < tree.mass ∧ At model .actual actual part.value := by
  have path := usable_path packet queries shape recorded usable
  obtain ⟨value,seen⟩ := (usable.2 model valid).1
  obtain ⟨part,bounded,equal⟩ := observed_path path tree meaning.2 seen
  refine ⟨part,by omega,⟨⟨value,seen⟩,?_⟩⟩
  intro other observed
  exact approx_left (path_unique path (at_unique meaning) other value observed seen) equal

theorem needed_not_output (packet : Packet roles)
    (arguments : ∀ clause ∈ packet.declaration.requirements, ApplicationArgs clause.arguments)
    (needed : Needed packet name) : name ∉ packet.declaration.outputNames := by
  obtain ⟨clause,present,member⟩ := needed
  rw [normalize_applicationArgs clause.arguments (arguments clause present)] at member
  exact fun output => packet.checked.outputOnly.2 clause present name output member

theorem simultaneous_trees (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds model)
    (queries : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = [query])
    (shape : QueryShape query) (recorded : packet.site.inputs[0]? = some (some origin))
    (tree : Tree) (meaning : At model .actual origin tree.value)
    (generation : GenerationGuard state packet)
    (arguments : ∀ clause ∈ packet.declaration.requirements, ApplicationArgs clause.arguments) :
    ∃ labels : Nat → Tree, ∀ name, Needed packet name →
      (labels name).mass < tree.mass ∧ CaptureValue packet model name (labels name).value := by
  classical
  have available : ∀ name, Needed packet name → ∃ part : Tree,
      part.mass < tree.mass ∧ CaptureValue packet model name part.value := by
    intro name needed
    obtain ⟨actual,usable⟩ := generation name needed
    obtain ⟨part,small,readback⟩ := captured_tree packet model valid queries shape recorded tree meaning usable
    exact ⟨part,small,GeneralNominalGroundProduction.capture_value packet model valid
      (needed_not_output packet arguments needed) usable readback⟩
  let labels : Nat → Tree := fun name => if needed : Needed packet name then
    Classical.choose (available name needed) else .scalar .int
  refine ⟨labels,?_⟩
  intro name needed
  simpa only [labels,dite_eq_left needed] using Classical.choose_spec (available name needed)

end Yulang.GeneralNominalBranchingLabels
