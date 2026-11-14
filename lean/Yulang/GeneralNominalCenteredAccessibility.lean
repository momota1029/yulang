import Yulang.GeneralNominalCenteredEnumeration

/-! Unrestricted centered accessibility from the retrospective depth bound.
One finite basis covers semantic installations and every administrative gain. -/
namespace Yulang.GeneralNominalCenteredAccessibility
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredTrace GeneralNominalCenteredAncestry GeneralNominalCenteredEnumeration
open GeneralNominalSaturationState (Packet Generated)
open GeneralNominalActualTraceSupport (pool)
open GeneralNominalOccurrenceEnumeration (basis)
open GeneralNominalSharedBudget (Signature Represents)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

structure SignatureCover (registry : Registry) (root : Occurrence roles) (start : State roles) where
  basis : List (Signature roles)
  covers : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ plan : Plan roles, ∀ support,
      Generated state.erased.current root plan.packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet → PacketGuard state plan support →
      ∃ signature ∈ basis, Represents signature plan.packet

def signatureCover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit) : SignatureCover registry root (initial context root) where
  basis := (GeneralNominalPacketCodes.codes context registry (GeneralNominalOccurrenceEnumeration.checkedFor checked source)
    (GeneralNominalOccurrenceEnumeration.basis checked source limit) (pool registry context root limit)).map
      (GeneralNominalPacketCodes.signature context)
  covers := by
    intro state path plan support generated enabled novel guard
    have registrySame := enabled.1.1
    have parent := GeneralNominalCenteredEnumeration.sites_enumerated checked source bound path plan.packet.site enabled.1.2.2.1
    have config := configuration_trace path
    rw [← enabled.1.2.1] at config
    have listed : ∀ slot, plan.packet.context.state.base.source slot ∈ pool registry context root limit := by
      rw [enabled.1.2.1]
      exact slot_pool source bound path
    have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
      simpa only [registrySame] using enabled.1.2.2.2.1
    have packetChecked : ∀ declaration ∈ plan.packet.registry.declarations,
        DeclarationChecked plan.packet.registry.constructors roles declaration := by
      rw [registrySame]; exact GeneralNominalOccurrenceEnumeration.checkedFor checked source
    have codeMember := GeneralNominalPacketCodes.encoded_member context plan.packet packetChecked parent visible
      enabled.1.2.2.2.2.2.1 listed config.2.1.symm config.2.2.symm
    have represented := GeneralNominalPacketCodes.encode_represents context plan.packet config.1.symm config.2.1.symm config.2.2.symm
    refine ⟨_,?_,represented⟩
    have mapped := (List.mem_map (f := GeneralNominalPacketCodes.signature context)).mpr ⟨_,codeMember,rfl⟩
    subst registry
    exact mapped

inductive Fact (roles : Roles.RoleDecls) where
  | signature : Signature roles → Fact roles
  | known : Nat → Fact roles
  | alias : Nat → Nat → Fact roles
  | equal : Nat → Nat → Fact roles
  | point : Nat → Fact roles

def Holds (state : State roles) : Fact roles → Prop
  | .signature signature => GeneralNominalSharedBudget.Holds state.erased signature
  | .known identity => GeneralNominalState.Known state.erased.current.context.state identity
  | .alias first last => GeneralNominalSaturationState.Alias state.erased.current first last
  | .equal first last => GeneralNominalFeedbackSteps.RawEqual state.erased.current first last
  | .point identity => GeneralNominalReobservationOrder.Point state.erased.current identity

theorem monotone (step : Step registry root before after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  have growth := at_extends step.choose_spec.2
  cases fact with
  | signature signature =>
    intro known
    exact ⟨fun model valid => known.1 model (growth.journal.models model valid),
      fun child member => growth.journal.edges _ (known.2 child member)⟩
  | known => exact growth.journal.known _
  | equal => exact fun prior model valid => prior model (growth.ordinary model valid)
  | alias first last => exact GeneralNominalSaturationProgress.monotone growth.journal (.alias first last)
  | point => exact point_at step.choose_spec.2

def facts (signatures : List (Signature roles)) (sources : List Nat) (occurrences : List (Occurrence roles)) : List (Fact roles) :=
  signatures.map .signature ++ (sources.map .known ++
    (sources.flatMap (fun first => sources.map (.equal first)) ++
      (sources.map .point ++ occurrences.flatMap (fun first => occurrences.map (fun last => .alias first.identity last.identity)))))

theorem signature_mem (member : signature ∈ signatures) : Fact.signature signature ∈ facts signatures sources occurrences :=
  List.mem_append_left _ (List.mem_map.mpr ⟨signature,member,rfl⟩)

theorem known_mem (member : identity ∈ sources) : @Fact.known roles identity ∈ facts signatures sources occurrences :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨identity,member,rfl⟩))

theorem equal_mem (one : first ∈ sources) (two : last ∈ sources) :
    @Fact.equal roles first last ∈ facts signatures sources occurrences :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨first,one,List.mem_map.mpr ⟨last,two,rfl⟩⟩)))

theorem point_mem (member : identity ∈ sources) : @Fact.point roles identity ∈ facts signatures sources occurrences :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨identity,member,rfl⟩))))

theorem alias_mem (one : first ∈ occurrences) (two : last ∈ occurrences) :
    @Fact.alias roles first.identity last.identity ∈ facts signatures sources occurrences :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨first,one,List.mem_map.mpr ⟨last,two,rfl⟩⟩))))

theorem progress (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (step : Step registry root before after) :
    ∃ fact ∈ facts (signatureCover checked source bound).basis
      (pool registry context root limit) (basis checked source limit), ¬ Holds before fact ∧ Holds after fact := by
  have supported := source_pool source bound path
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install plan support enabled novel guard =>
    obtain ⟨signature,member,represents⟩ := (signatureCover checked source bound).covers before path plan support generated enabled novel guard
    exact ⟨.signature signature,signature_mem member,
      GeneralNominalSharedBudget.novel_signature enabled novel represents,
      GeneralNominalSharedBudget.installed_signature represents support⟩
  | refresh focus context certificate identity member unknown known =>
    exact ⟨.known identity,known_mem (supported.1 member),unknown,known⟩
  | merge first last support one two same novel guard =>
    obtain ⟨a,ha,ea⟩ := centered_site_registered path first one
    obtain ⟨b,hb,eb⟩ := centered_site_registered path last two
    have firstMem : first.occurrence ∈ basis checked source limit := ea ▸ sites_enumerated checked source bound path a ha
    have lastMem : last.occurrence ∈ basis checked source limit := eb ▸ sites_enumerated checked source bound path b hb
    exact ⟨.alias first.occurrence.identity last.occurrence.identity,alias_mem firstMem lastMem,novel,
      GeneralNominalCycleSteps.merged_inputs before.erased.current first.observed last.observed⟩
  | administrative focus after action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := generated_registered path generated
      exact False.elim (absent site member same)
    | refresh context certificate identity member unknown known =>
      exact ⟨.known identity,known_mem (supported.1 member),unknown,known⟩
    | equate first last one two equal novel =>
      exact ⟨.equal first last,equal_mem (supported.1 one) (supported.1 two),novel,
        GeneralNominalFeedbackSteps.equate_feedback before.erased.current first last⟩
    | reobserve revision certificate improved =>
      obtain ⟨slot,old,now⟩ := improved.2
      refine ⟨.point (before.erased.current.context.state.base.source slot),
        point_mem (slot_pool source bound path slot),?_,slot,rfl,now⟩
      rintro ⟨other,same,point⟩
      have equal := before.erased.current.context.state.base.source_injective same
      exact old (equal ▸ point)

theorem accessible_of_installed_depth_bound (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalFiniteProgress.accessible (Step registry root) (initial context root) Holds
    (facts (signatureCover checked source bound).basis (pool registry context root limit) (basis checked source limit))
    (fun _ _ step => monotone step) (fun _ _ path step => progress checked source bound path step)

theorem ground_point_root_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  accessible_of_installed_depth_bound checked source (installed_depth_bound point ground)

theorem initial_source_accessible (checked : Checked registry)
    (source : InitialSource registry root state)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : ∀ context, GeneralNominalSourceFormation.InitialSource registry context root →
      state = initial context root → ∃ labels, GeneralNominalGroundAccessibility.GroundRoots context root labels) :
    Acc (fun next current => Step registry root current next) state := by
  obtain ⟨context,formed,equal⟩ := GeneralNominalCenteredPointSource.initial_unique source point
  obtain ⟨labels,finite⟩ := ground context formed equal
  subst state
  exact ground_point_root_accessible checked formed point finite

end Yulang.GeneralNominalCenteredAccessibility
