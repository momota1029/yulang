import Yulang.B4SkeletonV5
import Yulang.GeneralDictionarySupportJournal
import Yulang.GeneralDictionaryOrdinaryTrace
import Yulang.GeneralDictionarySupportEvidence

/-! Joint-free generation for selections already represented by a historical
packet across an ordinary-context extension. This is a structural result: no
model, Evidence, semantic replay, or Joint premise is needed. Unrestricted
point reobservation is not an ordinary extension and remains outside the result.
The general V5 GeneratedChildren field is NOT closed by this module. -/
namespace Yulang.GeneralDictionarySupportGeneratedChildren
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

theorem children_extend (state : GeneralNominalState.State) (registry : Registry)
    (focus : Occurrence roles) (declaration : Declaration)
    (check : DeclarationChecked constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings)
    (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
    (allocated : List GeneralNominalIdentities.Origin) :
    GeneralNominalAllocation.children
      (GeneralDictionaryOrdinaryTransport.extendState state reserved atoms allocated)
      registry focus declaration check bindings =
    GeneralNominalAllocation.children state registry focus declaration check bindings := by
  rfl

/-- Actual installation stores the argument lookup used to construct a packet.
Unlike a semantic Instance this provenance needs no inhabited model class. -/
theorem packet_arguments (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets,
      GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds := by
  induction formed with
  | initial context source => intro packet member; cases member
  | update formed update ih =>
    intro packet member
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | administrative _ _ admin => cases admin <;> exact ih packet member
    | merge => exact ih packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact enabled.1.2.2.2.2.2.1
      · exact ih packet old

/-- Fixed-view ordinary growth preserves the syntactic children of a recorded
selection, even if no model exists after the growth. Freshness and branch
feasibility are supplied only by the CURRENT survivor, not transported. -/
theorem selected_children_eq (registry : Registry) (checked : Checked registry)
    (state : Tracked roles) (root focus : Occurrence roles)
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets)
    (same : packet.site.occurrence = focus)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (key : Nat) (children : List (Occurrence roles))
    (identity : packet.declaration.id = key)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    children = packet.children := by
  have arguments := packet_arguments registry root state formed packet recorded
  have visible := GeneralDictionarySupportJournal.packet_visible registry root state formed packet recorded
  have reg := GeneralDictionarySupportJournal.packet_registry registry root state formed packet recorded
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨reserved,atoms,allocated,growth⟩ := growth
  rw [growth] at survivor
  obtain ⟨_,declaration,present,check,id,role,bounds,located,prepared,kids⟩ := survivor
  have decl := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked declaration packet.declaration
    present visible (id.trans identity.symm)
  subst declaration
  rw [← same] at located kids
  have eq : bounds = packet.bounds := Option.some.inj (located.symm.trans arguments)
  subst bounds
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.bindings_report] at kids
  rw [children_extend] at kids
  simpa only [Packet.children,Packet.bindings,reg] using kids

/-- Reachability supplies historical edges. Stability, Joint, and a model are
not required when the actual selected key is already stored and the inspection
view has only ordinary growth since that packet. -/
theorem recorded_selected_generated (registry : Registry) (checked : Checked registry)
    (state : Tracked roles) (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (reached : Generated state.current root focus)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (same : packet.site.occurrence = focus)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (key : Nat) (children : List (Occurrence roles))
    (identity : packet.declaration.id = key)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    ∀ child ∈ children, Generated state.current root child := by
  have formed := GeneralNominalSupportBoundary.reachable_formed registry state root reachable
  have kids := selected_children_eq registry checked state root focus formed packet recorded same growth key children identity selected
  intro child member
  rw [kids] at member
  have generated := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet recorded).2 child member
  rw [same] at generated
  exact generated_trans reached generated

/-- A syntactic certificate involving the recorded key and observation context,
not children, Models, Evidence, or the conclusion of GeneratedChildren. -/
def RecordedAt (state : Tracked roles) (focus : Occurrence roles) (key : Nat) : Prop :=
  ∃ packet ∈ state.current.packets, packet.site.occurrence = focus ∧
    packet.declaration.id = key ∧
    GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context

/-- Joint is only needed for nonterminal selections not covered by a stored key
at an ordinary extension. This residual is NOT proved for arbitrary reaches. -/
def UnrecordedNonterminalJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (GeneralNominalSupportBoundary.boundary roles).Checked registry → ∀ state root,
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state →
    ∀ focus, Generated state.current root focus →
      GeneralNominalSupportSteps.Stable registry state focus → ∀ key children,
        GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
        children ≠ [] → ¬ RecordedAt state focus key →
          GeneralNominalJointCandidates.Joint registry state.current focus key

/-- Actual V5 generation under the smaller residual. Terminal selections and
ordinary-transported recorded selections consume no Joint hypothesis. -/
theorem generatedChildren (roles : Roles.RoleDecls)
    (joint : UnrecordedNonterminalJoint roles) :
    B4SkeletonV5.GeneratedChildren (GeneralNominalSupportBoundary.boundary roles) := by
  classical
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.current root focus := by
    rcases reached with same | reached
    · subst focus; exact .root
    · exact reached
  have selected := (GeneralNominalSupportBoundary.local_correspondence registry state focus (.selected key children)).mp
    (B4TargetV3.Local.selected safe unique)
  by_cases covered : RecordedAt state focus key
  · obtain ⟨packet,recorded,same,id,growth⟩ := covered
    exact recorded_selected_generated registry checked.2 state root focus reachable generated
      packet recorded same growth key children id selected child member
  · have nonempty : children ≠ [] := by intro nil; rw [nil] at member; cases member
    have childrenGenerated := (GeneralDictionarySupportEvidence.reachable_joint_instance
      registry state root focus reachable key children stable selected
      (joint registry checked state root reachable focus generated stable key children selected nonempty covered)).2
    exact generated_trans generated (childrenGenerated child member)

end Yulang.GeneralDictionarySupportGeneratedChildren
