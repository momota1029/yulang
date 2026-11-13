import Yulang.GeneralNominalIdentityProvenance
import Yulang.GeneralNominalHoleElimination

/-! A source-derived singleton signature cover for identity leaves. This proves
accessibility of the existing shared relation, with no supplied finite basis.
Semantic progress is a previously missing alias between original source IDs. -/
namespace Yulang.GeneralNominalIdentityBudget
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSteps GeneralNominalSharedBudget
open GeneralNominalIdentityLeaf GeneralNominalIdentityProvenance
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : Tracked roles} {packet : Packet roles}

def Delta (root : Occurrence roles) (input : Nat) (model : Assignment) : Prop :=
  ∀ output ∈ root.demand.outputs, Equivalent (model output.target).1 (model input).1

theorem enabled_defined (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    GeneralNominalMaterialization.RootDefined packet.declaration packet.site.occurrence := by
  obtain ⟨_,_,_,bounds,_,_,ready,_⟩ := enabled.1.2.2.2.2.2.2.1
  exact ready.1

theorem delta_exact (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (model : Assignment) :
    (GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model) ↔
      Delta root input model := by
  have localShape := shape packet.declaration enabled.1.2.2.2.1
  obtain ⟨slot,bounds,source⟩ := enabled_bounds shape formed point enabled
  have site := enabled_site shape formed enabled
  have rootEq : packet.site.occurrence = root := congrArg GeneralNominalDemandMerging.Site.occurrence site
  have exactOutputs := outputs_exact localShape bounds model
  rw [source] at exactOutputs
  constructor
  · intro valid output member
    apply exactOutputs.mp valid.2 output.target
    apply target_complete (enabled_defined enabled)
    simpa only [rootEq] using member
  · intro valid
    refine ⟨inputs_valid localShape bounds model,exactOutputs.mpr ?_⟩
    intro target member
    obtain ⟨output,member,equal⟩ := target_requested member
    rw [rootEq] at member
    rw [← equal]
    exact valid output member

def signature (root : Occurrence roles) (input : Nat) : Signature roles :=
  ⟨root,[],Delta root input⟩

theorem represents (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    Represents (signature root input) packet :=
  ⟨(congrArg GeneralNominalDemandMerging.Site.occurrence (enabled_site shape formed enabled)).symm,
    (children_empty packet (shape packet.declaration enabled.1.2.2.2.1).terminal).symm,
    fun model => (delta_exact shape formed point enabled model).symm⟩

def AliasHeld (state : Tracked roles) (input target : Nat) : Prop :=
  ∀ model, Models state.current model → Equivalent (model target).1 (model input).1

theorem alias_monotone (step : Step registry root before after) (held : AliasHeld before input target) :
    AliasHeld after input target := fun model valid => held model (step_models step model valid)

theorem administrative_alias (action : Administrative registry state.current focus after) :
    AliasHeld {state with current := after} input target ↔ AliasHeld state input target := by
  constructor
  · intro held model valid
    exact held model ((GeneralNominalSupportSteps.administrative_models action model).mpr valid)
  · intro held model valid
    exact held model ((GeneralNominalSupportSteps.administrative_models action model).mp valid)

/-- A novel installation consumes a missing, nonreflexive source alias. -/
theorem genuine_alias (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet) (support : List (Occurrence roles)) :
    ∃ output ∈ root.demand.outputs, output.target ≠ input ∧ ¬ AliasHeld state input output.target ∧
      AliasHeld (install state packet support) input output.target := by
  classical
  have rep := represents shape formed point enabled
  have missing : ¬ ∀ output ∈ root.demand.outputs, AliasHeld state input output.target := by
    intro held
    apply novel_signature enabled novel rep
    refine ⟨fun model valid output member => held output member model valid,?_⟩
    intro child member; cases member
  have witness : ∃ output ∈ root.demand.outputs, ¬ AliasHeld state input output.target := by
    apply Classical.byContradiction
    intro absent
    apply missing
    intro output member
    apply Classical.byContradiction
    intro notHeld
    exact absent ⟨output,member,notHeld⟩
  obtain ⟨output,member,notHeld⟩ := witness
  refine ⟨output,member,?_,notHeld,?_⟩
  · intro same
    apply notHeld
    intro model valid
    rw [same]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro model valid
    exact (installed_signature rep support).1 model valid output member

/-- The replacement uses an initial input hole and removes the target hole;
there is no occurs cycle or constructor growth in this source class. -/
theorem elimination_closed (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (different : target ≠ input) :
    GeneralNominalHoleElimination.Closed ((basis context).erase target)
      (.leaf input) := by
  intro name member
  have equal : name = input := by simpa [GeneralNominalOriginTerms.Expr.leaves] using member
  subst name
  exact (List.mem_erase_of_ne different.symm).mpr ((initial_frontier point source).2.1)

theorem eliminated_absent (context : GeneralNominalCandidates.Context) (target : Nat) :
    target ∉ (basis context).erase target := (basis_distinct context).not_mem_erase

theorem elimination_source (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (member : output ∈ root.demand.outputs) : output.target ∈ GeneralNominalState.sources context.state :=
  source.linked.2 output member

/-- Each actual transition either preserves its models or adds precisely the
fixed source alias conjunction. No allocated numeric ID occurs in this delta. -/
theorem step_semantics (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (step : Step registry root state after) :
    (∀ model, Models after.current model ↔ Models state.current model) ∨
      (∀ model, Models after.current model ↔ Models state.current model ∧ Delta root input model) := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus next action =>
      exact Or.inl (GeneralNominalSupportSteps.administrative_models action)
  | merge first last support one two same novel guard =>
      rw [formed_sites shape formed] at one two
      cases List.mem_singleton.mp one
      cases List.mem_singleton.mp two
      exact False.elim (novel (.refl _))
  | install packet support enabled novel guard =>
      right
      intro model
      rw [install_models enabled.1.2.1 model,GeneralNominalPacketSupport.packet_exact]
      rw [delta_exact shape formed point enabled model]
      constructor
      · rintro ⟨valid,_,delta⟩; exact ⟨valid,delta⟩
      · rintro ⟨valid,delta⟩
        exact ⟨valid,by simpa only [enabled.1.2.1] using valid.1,delta⟩

/-- A finite source-refinement budget expressed as exact model classes. This
avoids postulating a producer of an abstract elimination trace. -/
theorem source_refinement (shape : RegistryShape registry) (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state) :
    SourceFormed registry root state ∧
      ((∀ model, Models state.current model ↔ GeneralNominalState.Models context.state model) ∨
       (∀ model, Models state.current model ↔ GeneralNominalState.Models context.state model ∧ Delta root input model)) := by
  induction path with
  | refl => exact ⟨.initial context source,Or.inl (initial_models context root)⟩
  | tail path step ih =>
      refine ⟨.update ih.1 step,?_⟩
      rcases step_semantics shape ih.1 point step with same | add
      · rcases ih.2 with old | old
        · exact Or.inl (fun model => (same model).trans (old model))
        · exact Or.inr (fun model => (same model).trans (old model))
      · right
        intro model
        rw [add model]
        rcases ih.2 with old | old
        · rw [old model]
        · rw [old model]
          simp only [and_assoc,and_self]

theorem installed_readback (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (member : output ∈ root.demand.outputs) (support : List (Occurrence roles)) :
    GeneralNominalHoleReadback.Over (Models (install state packet support).current)
      ((basis context).map GeneralNominalRecursiveInspection.Origin.source) (.source output.target) (.leaf (.source input)) := by
  refine ⟨?_,?_⟩
  · intro model valid
    have equal := (installed_signature (represents shape formed point enabled) support).1 model valid output member
    refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
    intro a b one two; cases one; cases two; exact equal
  · intro origin member
    have same : origin = .source input := by simpa [GeneralNominalOriginTerms.Expr.leaves] using member
    subst origin
    exact List.mem_map.mpr ⟨input,(initial_frontier point source).2.1,rfl⟩

def cover (shape : RegistryShape registry) (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    SignatureCover registry root (GeneralNominalSupport.initial context root) where
  basis := [signature root input]
  covers state path packet support generated enabled novel guard := by
    have formed : SourceFormed registry root state := by
      clear generated enabled novel guard
      induction path with
      | refl => exact .initial context source
      | tail _ step ih => exact .update ih step
    exact ⟨signature root input,by simp,represents shape formed point enabled⟩

theorem cover_size (shape : RegistryShape registry) (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    (cover shape point source).basis.length = 1 := rfl

/-- This is the restricted source-budget theorem; the registry may be nonempty
and associated outputs may add equations to different source identities. -/
theorem source_budget (shape : RegistryShape registry) (_checked : Checked registry)
    (point : Point root input) (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    Nonempty (SignatureCover registry root (GeneralNominalSupport.initial context root)) :=
  ⟨cover shape point source⟩

theorem checked_initial_accessible (shape : RegistryShape registry) (checked : Checked registry)
    (point : Point root input) (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) := by
  obtain ⟨basis⟩ := source_budget shape checked point source
  exact accessible_of_signature_cover basis (.initial context source)

/-- Even arbitrary later observations and support choices cannot enable a
second novel installation for this root. -/
theorem no_second_installation (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet) (guard : PacketGuard state packet support)
    (path : B4Target.Steps (Step registry root) (install state packet support) after)
    (next : GeneralNominalFeedbackSteps.Installable registry after.current later) :
    GeneralNominalFeedbackSteps.Committed after.current later := by
  have current : SourceFormed registry root (install state packet support) :=
    .update formed ⟨packet.site.occurrence,generated,.install packet support enabled novel guard⟩
  have held := installed_signature (state := state) (represents shape formed point enabled) support
  have facts : SourceFormed registry root after ∧ Holds after (signature root input) := by
    clear next
    induction path with
    | refl => exact ⟨current,held⟩
    | tail _ step ih => exact ⟨.update ih.1 step,holds_monotone step ih.2⟩
  apply Classical.byContradiction
  intro missing
  exact novel_signature next missing (represents shape facts.1 point next) facts.2

end Yulang.GeneralNominalIdentityBudget
