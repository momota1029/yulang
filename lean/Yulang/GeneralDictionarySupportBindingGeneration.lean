import Yulang.GeneralDictionarySupportGeneratedChildren

/-! Syntactic capture suffices for historical child generation. Actual support
traces preserve the allocation seed, so no fixed carrier, unchanged view,
ordinary Extension, full-report equality, model or Joint is required. Only the
current argument lookup and its SOURCE-ID capture bindings must agree with the
recorded packet. This condition remains explicit and is not universal. -/
namespace Yulang.GeneralDictionarySupportBindingGeneration
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionarySupportGeneratedChildren
variable {roles : Roles.RoleDecls}

/-- Even arbitrary certified carrier-changing refresh preserves the seed. -/
theorem at_seed {registry : Registry} {before after : Tracked roles} {focus : Occurrence roles}
    (update : At registry before focus after) :
    after.current.context.state.seed = before.current.context.state.seed := by
  cases update with
  | administrative _ _ action =>
    cases action with
    | enqueue => rfl
    | refresh _ certificate _ _ _ _ => exact certificate.refines.seed
    | equate => rfl
    | reobserve => rfl
  | install packet support enabled _ _ =>
    change packet.context.state.seed = before.current.context.state.seed
    rw [enabled.1.2.1]
  | merge => rfl

/-- Historical and current allocation seeds agree on every actually recorded
packet, without restrictions on intervening administrative transitions. -/
theorem packet_seed (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets,
      state.current.context.state.seed = packet.context.state.seed := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed update ih =>
    intro packet member
    obtain ⟨focus,generated,action⟩ := update
    have retained : ∀ p ∈ before.current.packets,
        after.current.context.state.seed = p.context.state.seed :=
      fun p member => (at_seed action).trans (ih p member)
    cases action with
    | administrative _ _ admin => cases admin <;> exact retained packet member
    | merge => exact retained packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · rfl
      · exact retained packet old

/-- Allocation depends on the state only through its stable seed when the
source-ID bindings are fixed. The carrier size and view may differ. -/
theorem children_seed (before after : GeneralNominalState.State)
    (seed : after.seed = before.seed) (registry : Registry) (focus : Occurrence roles)
    (declaration : Declaration) (check : DeclarationChecked constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children after registry focus declaration check bindings =
      GeneralNominalAllocation.children before registry focus declaration check bindings := by
  unfold GeneralNominalAllocation.children
  have frames : GeneralNominalAllocation.frame (roles := roles) after registry focus.identity bindings =
      GeneralNominalAllocation.frame before registry focus.identity bindings := by
    unfold GeneralNominalAllocation.frame GeneralNominalAllocation.capture GeneralNominalAllocation.allocation
      GeneralNominalAllocation.source
    rw [seed]
  rw [frames]

/-- Finite syntactic witness. No Survivor, semantic equality or child-generation
predicate occurs; only the computed source-ID capture list is compared. -/
def BindingsAt (packet : Packet roles) (current : GeneralNominalCandidates.Context) : Prop :=
  ∃ bounds, GeneralNominalRecursiveCandidates.arguments current packet.site.occurrence = some bounds ∧
    GeneralNominalRecursiveInspection.bindings current.state
      (GeneralNominalRecursiveCandidates.report current packet.declaration bounds) = packet.bindings

/-- The earlier ordinary-growth certificate implies the weaker binding witness. -/
theorem bindings_of_extension (packet : Packet roles) (current : GeneralNominalCandidates.Context)
    (arguments : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context current) : BindingsAt packet current := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  refine ⟨packet.bounds,arguments,?_⟩
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.bindings_report]
  rfl

/-- Selected emission agrees with a stored key whenever computed bindings
agree. Actual provenance discharges the seed and visible-declaration facts. -/
theorem selected_children_eq (registry : Registry) (checked : Checked registry)
    (state : Tracked roles) (root focus : Occurrence roles)
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (captures : BindingsAt packet state.current.context) (key : Nat) (children : List (Occurrence roles))
    (identity : packet.declaration.id = key)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    children = packet.children := by
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨_,declaration,present,check,id,role,bounds,located,prepared,kids⟩ := survivor
  have decl := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked declaration packet.declaration
    present (GeneralDictionarySupportJournal.packet_visible registry root state formed packet recorded)
    (id.trans identity.symm)
  subst declaration
  obtain ⟨oldBounds,found,captures⟩ := captures
  rw [same] at found
  have equal := Option.some.inj (located.symm.trans found)
  subst oldBounds
  rw [captures,← same] at kids
  rw [children_seed packet.context.state state.current.context.state
    (packet_seed registry root state formed packet recorded)] at kids
  simpa only [Packet.children,GeneralDictionarySupportJournal.packet_registry registry root state formed packet recorded] using kids

/-- General reachable support state, not an ordinary-trace subrelation. -/
theorem recorded_selected_generated (registry : Registry) (checked : Checked registry)
    (state : Tracked roles) (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (reached : Generated state.current root focus) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (captures : BindingsAt packet state.current.context) (key : Nat) (children : List (Occurrence roles))
    (identity : packet.declaration.id = key)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    ∀ child ∈ children, Generated state.current root child := by
  have formed := GeneralNominalSupportBoundary.reachable_formed registry state root reachable
  have kids := selected_children_eq registry checked state root focus formed packet recorded same captures key children identity selected
  intro child member
  rw [kids] at member
  have generated := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet recorded).2 child member
  rw [same] at generated
  exact generated_trans reached generated
/-- A current binding certificate attached to an actually recorded key. -/
def RecordedBindingsAt (state : Tracked roles) (focus : Occurrence roles) (key : Nat) : Prop :=
  ∃ packet ∈ state.current.packets, packet.site.occurrence = focus ∧
    packet.declaration.id = key ∧ BindingsAt packet state.current.context

theorem recordedAt_implies_bindings (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (focus : Occurrence roles) (key : Nat) (covered : RecordedAt state focus key) :
    RecordedBindingsAt state focus key := by
  obtain ⟨packet,member,same,id,growth⟩ := covered
  exact ⟨packet,member,same,id,bindings_of_extension packet state.current.context
    (packet_arguments registry root state formed packet member) growth⟩

/-- The residual excludes terminal and binding-covered selections. Compared to
UnrecordedNonterminalJoint, the excluded recorded class permits arbitrary
carrier/view changes, provided the selected source-ID capture list is stable. -/
def UncoveredBindingsJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (GeneralNominalSupportBoundary.boundary roles).Checked registry → ∀ state root,
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state →
    ∀ focus, Generated state.current root focus →
      GeneralNominalSupportSteps.Stable registry state focus → ∀ key children,
        GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
        children ≠ [] → ¬ RecordedBindingsAt state focus key →
          GeneralNominalJointCandidates.Joint registry state.current focus key

theorem generatedChildren (roles : Roles.RoleDecls) (joint : UncoveredBindingsJoint roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalSupportBoundary.boundary roles) := by
  classical
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.current root focus := by
    rcases reached with same | reached
    · subst focus; exact .root
    · exact reached
  have selected := (GeneralNominalSupportBoundary.local_correspondence registry state focus (.selected key children)).mp
    (B4TargetV3.Local.selected safe unique)
  by_cases covered : RecordedBindingsAt state focus key
  · obtain ⟨packet,recorded,same,id,captures⟩ := covered
    exact recorded_selected_generated registry checked.2 state root focus reachable generated
      packet recorded same captures key children id selected child member
  · have nonempty : children ≠ [] := by intro nil; rw [nil] at member; cases member
    have childrenGenerated := (GeneralDictionarySupportEvidence.reachable_joint_instance
      registry state root focus reachable key children stable selected
      (joint registry checked state root reachable focus generated stable key children selected nonempty covered)).2
    exact generated_trans generated (childrenGenerated child member)
end Yulang.GeneralDictionarySupportBindingGeneration
