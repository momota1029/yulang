import Yulang.GeneralDictionaryCycleEvidence
import Yulang.GeneralNominalFeedbackBoundary

/-! Existing source evidence on the actual feedback boundary. Joint applicability
is an explicit residual, restricted to inhabited journals for EvidenceNode.
No new stability or evidence judgment is substituted for the source judgment. -/
namespace Yulang.GeneralDictionaryFeedbackEvidence

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps
open GeneralNominalJointCandidates (Joint)
open GeneralNominalDemandMerging (Site)
open GeneralDictionaryReadback (Payload)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls}

abbrev evidence (roles : Roles.RoleDecls) : GeneralNominalFeedbackBoundary.Evidence roles :=
  fun registry state => GeneralDictionaryRecursiveEvidence.Evidence registry state.context

abbrev boundary (roles : Roles.RoleDecls) :=
  GeneralNominalFeedbackBoundary.boundary roles (evidence roles)

/-- Recovery changes only missing origins, never an existing source origin. -/
theorem recover_inputs (state : State roles) (site : Site roles)
    (known : ∀ input ∈ site.inputs, input ≠ none) :
    (GeneralNominalFeedbackSites.recover state site).inputs = site.inputs := by
  apply List.ext_getElem
  · simp [GeneralNominalFeedbackSites.recover,site.arity]
  · intro index one two
    have bound : index < (roles site.occurrence.demand.role).arity := by
      simpa only [GeneralNominalFeedbackSites.recover,List.length_ofFn] using one
    have present := known (site.inputs[index]) (List.getElem_mem two)
    cases entry : site.inputs[index] with
    | none => exact False.elim (present entry)
    | some origin =>
      simp [GeneralNominalFeedbackSites.recover,GeneralNominalFeedbackSites.recoverOrigin,entry]

/-- Every old same-input merge remains enabled after provenance recovery. -/
theorem sameInputs_recovered (state : State roles) (first last : Site roles)
    (same : GeneralNominalDemandMerging.SameInputs (Models state) first last) :
    GeneralNominalFeedbackSites.SameInputs state first last := by
  have known : ∀ xs ys, GeneralNominalDemandMerging.All₂
      (GeneralNominalDemandMerging.Related (Models state)) xs ys →
      (∀ input ∈ xs, input ≠ none) ∧ (∀ input ∈ ys, input ≠ none) := by
    intro xs ys related
    induction related with
    | nil => simp
    | cons head tail ih =>
      obtain ⟨a,b,rfl,rfl,_⟩ := head
      constructor
      · intro input member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact ih.1 input member
      · intro input member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact ih.2 input member
  have all := known _ _ same.2
  exact ⟨same.1,by simpa only [recover_inputs state first all.1,recover_inputs state last all.2] using same.2⟩

/-- Stable feedback registers every linked root. -/
theorem stable_site (registry : Registry) (state : State roles) (root : Occurrence roles)
    (stable : Stable registry state root)
    (linked : GeneralNominalState.Linked state.context.state root.demand) :
    ∃ site ∈ state.sites, site.occurrence = root := by
  classical
  apply Classical.byContradiction
  intro missing
  have absent : ∀ site ∈ state.sites, site.occurrence ≠ root := by
    intro site member same
    exact missing ⟨site,member,same⟩
  exact stable root .root _ (.enqueue root linked absent)

/-- Stable + real feedback selection + joint applicability commits the actual
current-context packet, including both old and recovered merge guards. -/
theorem stable_joint_packet (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (joint : Joint registry state root key) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Installable registry state packet ∧ Committed state packet := by
  obtain ⟨model,valid,branch,_⟩ := joint.2
  obtain ⟨declaration,visible,checked,identity,role,prepared,bounds,located,holds⟩ := branch
  obtain ⟨site,member,same⟩ := stable_site registry state root stable prepared.2.1
  let packet : Packet roles := ⟨registry,state.context,site,declaration,checked,bounds⟩
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.context root key packet.children := by
    refine ⟨?_,declaration,visible,checked,identity,role,bounds,located,prepared,?_⟩
    · cases selected with | selected safe _ => exact safe.1
    · change GeneralNominalAllocation.children state.context.state registry site.occurrence declaration checked _ = _
      rw [same]
      rfl
  have exactChildren : packet.children = children := by
    cases selected with | selected _ unique => exact (unique.2 key packet.children survivor).2
  have localRule : GeneralNominalFeedbackK2.Local registry state site.occurrence
      (.selected declaration.id packet.children) := by
    rw [same,identity,exactChildren]
    exact selected
  have merges : GeneralNominalFeedbackSteps.MergesClosed state site := by
    intro other present inputs
    exact stable_merges stable site other member present (same ▸ Generated.root) inputs
  have enabled : Installable registry state packet := by
    refine ⟨⟨rfl,rfl,member,visible,?_,?_,?_,?_,?_,?_,?_,?_⟩,localRule,merges⟩
    · simpa only [packet,same] using role
    · simpa only [packet,same] using located
    · simpa only [packet,same] using prepared
    · exact GeneralNominalFeedbackK2.selected_legacy localRule
    · intro prior present alias
      apply identity.trans
      apply Eq.symm
      apply joint.1 prior present
      simpa only [packet,same] using alias
    · intro other present inputs
      exact merges other present (sameInputs_recovered state site other inputs)
    · refine ⟨model,valid,?_⟩
      simpa only [Packet.Holds,packet,same] using holds
    · simpa only [packet,same,identity] using joint
  exact ⟨packet,rfl,rfl,same,identity,exactChildren,enabled,
    stable_committed stable packet (same ▸ Generated.root) enabled⟩

/-- Current source instances and actual generated edges in the same snapshot. -/
theorem stable_joint_instance (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (joint : Joint registry state root key) :
    (∀ model, Models state model → GeneralDictionaryRecursiveEvidence.Instance
      registry state.context model root key children) ∧
      ∀ child ∈ children, Generated state root child := by
  obtain ⟨packet,registrySame,contextSame,rootSame,keySame,childrenSame,enabled,committed⟩ :=
    stable_joint_packet registry state root key children stable selected joint
  constructor
  · intro model valid
    have source := GeneralDictionaryCommittedEvidence.committed_instance state packet
      (by simpa only [registrySame] using enabled.1.2.2.2.1)
      enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1 committed model valid
    simpa only [registrySame,contextSame,rootSame,keySame,childrenSame] using source
  · intro child member
    have source := GeneralDictionaryCommittedEvidence.committed_children state packet committed child
      (by simpa only [childrenSame] using member)
    simpa only [rootSame] using source

/-- Source child evidence uses the same arbitrary final model as the parent. -/
theorem stable_joint_evidence (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state root)
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (joint : Joint registry state root key)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.context model root key children dictionaries
    ((stable_joint_instance registry state root key children stable selected joint).1 model valid) given

/-- Evidence needs Joint only when the journal actually has a model. This is
not asserted for all stable source states or derived from source formation. -/
def ModeledSelectedJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ (state : State roles) (root : Occurrence roles) key children,
    Stable registry state root →
    GeneralNominalFeedbackK2.Local registry state root (.selected key children) →
    (∃ model, Models state model) → Joint registry state root key

/-- Generation is model-independent and therefore has the stronger residual. -/
def SelectedJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ (state : State roles) (root : Occurrence roles) key children,
    Stable registry state root →
    GeneralNominalFeedbackK2.Local registry state root (.selected key children) →
    Joint registry state root key

theorem evidenceNode_of_modeled_selected_joint (roles : Roles.RoleDecls)
    (joint : ModeledSelectedJoint roles) : B4SkeletonV4.EvidenceNode (boundary roles) := by
  intro registry checked state model valid root key children dictionaries stable _ safe unique given
  have selected := (GeneralNominalFeedbackBoundary.local_correspondence roles (evidence roles)
    registry state root _).mp (B4TargetV3.Local.selected safe unique)
  exact stable_joint_evidence registry state root key children stable selected
    (joint registry checked state root key children stable selected ⟨model,valid⟩) model valid dictionaries given

theorem generatedChildren_of_selected_joint (roles : Roles.RoleDecls)
    (joint : SelectedJoint roles) : B4SkeletonV4.GeneratedChildren (boundary roles) := by
  apply B4SkeletonV4.generatedChildren_of_direct_transitive
  · intro registry checked state root key children stable safe unique child member
    have selected := (GeneralNominalFeedbackBoundary.local_correspondence roles (evidence roles)
      registry state root _).mp (B4TargetV3.Local.selected safe unique)
    exact (stable_joint_instance registry state root key children stable selected
      (joint registry checked state root key children stable selected)).2 child member
  · intro _ _ _ _ _ _ first last
    exact generated_trans first last

/-- Every actual feedback trace preserves a committed packet's semantics and
recorded edges. The packet retains its original inspection context. -/
theorem committed_trace (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (packet : Packet roles)
    (committed : Committed before packet)
    (path : B4Target.Steps (Step registry root) before after) : Committed after packet := by
  induction path with
  | refl => exact committed
  | tail prior step ih =>
    refine ⟨fun model valid => ih.1 model (step_models step model valid),?_⟩
    intro child member
    exact (GeneralNominalFeedbackProgress.at_extends step.choose_spec.2).journal.edges _ (ih.2 child member)

/-- A real installation followed by arbitrary feedback updates retains the
original source instance and all emitted child edges in every final model. -/
theorem installed_trace_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (packet : Packet roles)
    (enabled : Installable registry before packet)
    (path : B4Target.Steps (Step registry root)
      (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) after) :
    (∀ model, Models after model → GeneralDictionaryRecursiveEvidence.Instance
      packet.registry packet.context model packet.site.occurrence packet.declaration.id packet.children) ∧
      ∀ child ∈ packet.children, Generated after packet.site.occurrence child := by
  have committed := committed_trace registry root _ after packet (installed_committed before packet) path
  exact ⟨fun model valid => GeneralDictionaryCommittedEvidence.committed_instance after packet
    (by simpa only [enabled.1.1] using enabled.1.2.2.2.1) enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 enabled.1.2.2.2.2.2.2.1 committed model valid,
    fun child member => GeneralDictionaryCommittedEvidence.committed_children after packet committed child member⟩

/-- Source formation supplies real source instances and generated child edges
for every recorded packet, throughout all feedback updates. Each packet is
interpreted at its stored source context, even after certified refresh. -/
theorem sourceFormed_recorded_instances (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.packets,
      (∀ model, Models state model → GeneralDictionaryRecursiveEvidence.Instance
        packet.registry packet.context model packet.site.occurrence packet.declaration.id packet.children) ∧
      ∀ child ∈ packet.children, Generated state packet.site.occurrence child := by
  induction formed with
  | initial context source =>
    intro packet member
    cases member
  | @update before after formed update ih =>
    obtain ⟨focus,generated,action⟩ := update
    have retain : ∀ packet ∈ before.packets,
        (∀ model, Models after model → GeneralDictionaryRecursiveEvidence.Instance
          packet.registry packet.context model packet.site.occurrence packet.declaration.id packet.children) ∧
        ∀ child ∈ packet.children, Generated after packet.site.occurrence child := by
      intro packet member
      have old := ih packet member
      exact ⟨fun model valid => old.1 model (at_models action model valid),
        fun child present => GeneralNominalSaturationSteps.generated_monotone
          (GeneralNominalFeedbackProgress.at_extends action).journal (old.2 child present)⟩
    intro packet member
    cases action with
    | enqueue => exact retain packet member
    | merge => exact retain packet member
    | refresh => exact retain packet member
    | equate => exact retain packet member
    | install installed enabled novel =>
      rcases List.mem_cons.mp member with rfl | old
      · exact installed_trace_instance registry root before _ packet enabled .refl
      · exact retain packet old

/-- Recorded packets belong to the same source registry throughout formation. -/
theorem sourceFormed_packet_registry (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.packets, packet.registry = registry := by
  induction formed with
  | initial context source => intro packet member; cases member
  | update formed update ih =>
    intro packet member
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | enqueue => exact ih packet member
    | merge => exact ih packet member
    | refresh => exact ih packet member
    | equate => exact ih packet member
    | install installed enabled novel =>
      rcases List.mem_cons.mp member with rfl | old
      · exact enabled.1.1
      · exact ih packet old

/-- Same-model child evidence completes any recorded packet at its original
inspection context in a source-formed final state. No Joint hypothesis remains. -/
theorem sourceFormed_recorded_evidence (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry packet.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry packet.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) := by
  have instanceRule := (sourceFormed_recorded_instances registry root state formed packet recorded).1 model valid
  rw [sourceFormed_packet_registry registry root state formed packet recorded] at instanceRule
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry packet.context model packet.site.occurrence
    packet.declaration.id packet.children dictionaries instanceRule given

end Yulang.GeneralDictionaryFeedbackEvidence
