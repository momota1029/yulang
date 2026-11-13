import Yulang.GeneralNominalIndexedOutputProduction

/-! Explicit inspection subtrees retain source labels and their hole set.
The real shared-capture guard gives one semantic value across repeated uses,
without identifying their different syntactic presentations. -/
namespace Yulang.GeneralNominalOpenCaptureLabels
open GeneralNominalOriginTerms GeneralNominalHeadMatchMass GeneralNominalOpenPatternLabels
open GeneralNominalOpenReification GeneralNominalHoleElimination GeneralNominalOpenInspectionMatching
open GeneralNominalRecursiveInspection GeneralNominalSharedCaptures GeneralNominalFiniteMeaning
open GeneralNominalSaturationState

variable {model : GeneralNominalCommonBridge.Assignment}

theorem child_closed (closed : Closed remaining (.node test children)) (index : Fin (arity test)) :
    Closed remaining (children index) := by
  intro name member
  exact closed name (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩)

theorem matched_labels (matched : Matches relation query term)
    (known : Label context pattern term) (closed : Closed remaining term) :
    Matches (fun name part => relation name part ∧ ∃ label, Label context label part ∧ Closed remaining part) query term := by
  induction matched generalizing pattern with
  | capture captured => exact .capture ⟨captured,pattern,known,closed⟩
  | scalar children => exact .scalar children
  | structural shape queries children matched ih =>
    apply Matches.structural
    intro index
    obtain ⟨source,_,label⟩ := child_source_label known index
    exact ih index label (child_closed closed index)
  | nominal name count queries children matched ih =>
    apply Matches.nominal
    intro index
    obtain ⟨source,_,label⟩ := child_source_label known index
    exact ih index label (child_closed closed index)

theorem shared_capture_value (packet : Packet roles) (branch : packet.Holds model)
    (guard : GenerationGuard tracked packet) (needed : Needed packet name)
    (captured : GeneralNominalOpenInspectionMatching.Captured values model (inheritedReport packet) name term) :
    GeneralNominalStructuralContainment.CaptureValue packet model name (denote values term) := by
  obtain ⟨bounds,origin,member,known⟩ := captured
  obtain ⟨representative,usable⟩ := guard name needed
  obtain ⟨actual,recorded,agree⟩ := usable.1.2 ⟨name,bounds,origin⟩ member rfl
  have meaning := known.2.2 actual recorded
  have shared := GeneralNominalSimultaneousCaptures.at_same meaning (same_symm (agree model branch))
  exact GeneralNominalGroundProduction.capture_value packet model branch
    (GeneralPatternVariableProvenance.needed_input packet needed) usable shared

/-- A fixed-hole input label and a successful real report suffice until an
opaque leaf is inspected. Every selected capture then has an original source
label, fixed-hole closure, and the guarded shared semantic value. -/
theorem inspect_labels_or_exposed (packet : Packet roles)
    (query : GeneralNominalInspection.Query) (bounds : GeneralNominalInspection.Bounds packet.context.state)
    (origin : Option Origin) (term : Expr Nat) (branch : packet.Holds model)
    (guard : GenerationGuard tracked packet)
    (valid : GeneralNominalState.Models packet.context.state model)
    (single : GeneralNominalInspectionAlignment.Single query)
    (finished : Finished (inspect packet.context.state query bounds origin))
    (known : GeneralNominalOpenInspectionPositions.Input values model packet.context.state bounds origin term)
    (included : Subreport (inspect packet.context.state query bounds origin) (inheritedReport packet))
    (label : Label context pattern term) (closed : Closed remaining term) :
    Matches (fun name part =>
      GeneralNominalOpenInspectionMatching.Captured values model (inheritedReport packet) name part ∧
      ∃ source, Label context source part ∧ Closed remaining part ∧
        (Needed packet name → GeneralNominalStructuralContainment.CaptureValue packet model name (denote values part))) query term ∨
      ∃ hole ∈ remaining, Exposed values model (inheritedReport packet) hole := by
  rcases inspect_matched_or_exposed packet.context.state model values (inheritedReport packet) valid
      query bounds origin term single finished known included with matched | ⟨hole,present,exposed⟩
  · have labels := matched_labels matched label closed
    left
    clear single finished known included label closed matched
    induction labels with
    | capture evidence =>
      obtain ⟨captured,source,label,closed⟩ := evidence
      exact .capture ⟨captured,source,label,closed,fun needed => shared_capture_value packet branch guard needed captured⟩
    | scalar children => exact .scalar children
    | structural shape queries children matched ih => exact .structural shape queries children ih
    | nominal name count queries children matched ih => exact .nominal name count queries children ih
  · exact Or.inr ⟨hole,closed hole present,exposed⟩

end Yulang.GeneralNominalOpenCaptureLabels
