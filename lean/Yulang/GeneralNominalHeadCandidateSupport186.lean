import Yulang.GeneralNominalHeadCandidateExtension186

/-! Support for a current uninstalled candidate. Head roots use only genuine
registered centers when role arities agree; the default index is unreachable.
Capture endpoints are old sources for singleton occurrences. Multiple or absent
occurrences allocate fresh merge endpoints, whose reservation is kept explicit. -/
namespace Yulang.GeneralNominalHeadCandidateSupport186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalHeadLedgerFrame182 (fullSources)
open GeneralNominalGeneratedSupport184 (Roots schema_roots roots_append)

 theorem schemas_bounded_roots (queries : List Query) (origins : Nat → Origin)
    (mode : Mode) (offset : Nat)
    (known : ∀ index, offset ≤ index → index < offset + queries.length → originSource (origins index) ∈ names) :
    Roots (schemas queries origins mode offset) names := by
  induction queries generalizing offset with
  | nil => simp [schemas,Roots]
  | cons query rest ih =>
    simp only [schemas]
    apply roots_append
    · exact schema_roots query (origins offset) mode (known offset (by omega) (by simp))
    · apply ih (offset+1)
      intro index lower upper
      apply known index (by omega)
      simp only [List.length_cons]
      omega

 theorem normalized_length (patterns : List GeneralDeclarationPatterns.Pattern) :
    (GeneralDeclarationPatterns.normalizeArgs patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simp only [GeneralDeclarationPatterns.normalizeArgs,List.length_cons,ih]

 theorem head_roots (plan : Plan roles)
    (aligned : plan.packet.declaration.role = plan.input.occurrence.demand.role) :
    Roots plan.headSchema (List.ofFn plan.input.center) := by
  apply schemas_bounded_roots
  intro index _ bound
  have length : (GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration).length =
      (roles plan.input.occurrence.demand.role).arity := by
    simp only [GeneralNominalInspection.queries,List.length_map,Declaration.normalHead,normalized_length]
    exact plan.packet.checked.signature.1.trans (congrArg (fun role => (roles role).arity) aligned)
  have valid : index < (roles plan.input.occurrence.demand.role).arity := by omega
  simp only [List.getElem?_ofFn,valid,↓reduceDIte,Option.getD_some,originSource]
  exact List.mem_ofFn.mpr ⟨⟨index,valid⟩,rfl⟩

 theorem current_source (state : State roles) (member : name ∈ GeneralNominalState.sources state.core.erased.current.context.state) :
    name ∈ fullSources state := by
  simp [fullSources,GeneralNominalModeLedger181.fullSources,GeneralNominalRawFrame179.rawSources,member]

 theorem registered_center (state : State roles) (site : Site roles)
    (registered : site ∈ state.core.sites) (member : name ∈ List.ofFn site.center) :
    name ∈ fullSources state := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  have inside : site.center index ∈ GeneralNominalCenteredFrame179.siteSources site :=
    List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩
  have ledger : site.center index ∈ state.core.sites.flatMap GeneralNominalCenteredFrame179.siteSources :=
    List.mem_flatMap.mpr ⟨site,registered,inside⟩
  simp [fullSources,GeneralNominalModeLedger181.fullSources,GeneralNominalModeLedger181.ledgerSources,ledger]

 theorem candidate_origin (state : State roles) (candidate : Plan roles)
    (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) :
    originSource entry.origin ∈ fullSources state :=
  registered_center state candidate.input registered ((head_roots candidate aligned).2 entry present)

 theorem singleton_endpoints (state : State roles) (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (name : Nat) (bounds : GeneralSourceState.Interval)
    (singleton : GeneralNominalAllocation.occurrences candidate.packet.bindings name = [bounds]) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ∈ fullSources state ∧
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2 ∈ fullSources state := by
  have endpoints := GeneralNominalAllocationSupport.occurrences_endpoints
    (GeneralNominalAllocationSupport.report_endpoints candidate.packet.context.state
      (GeneralNominalPacketSupport.report candidate.packet)) name bounds
    (by change bounds ∈ GeneralNominalAllocation.occurrences candidate.packet.bindings name
        rw [singleton]; exact List.mem_cons_self ..)
  change (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).1 ∈ _ ∧
    (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).2 ∈ _
  simp only [GeneralNominalAllocation.capture,singleton]
  rw [current] at endpoints
  exact ⟨current_source state endpoints.1,current_source state endpoints.2⟩

/-- Fresh high-namespace names are disjoint from every current candidate
capture endpoint, including newly allocated merge endpoints. Registration of
the candidate packet itself is not required. -/
theorem current_capture_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles)
    (current : packet.context = state.core.erased.current.context)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [current]
    intro present
    apply GeneralNominalHeadRawSeparation185.wf_raw_separate reachable high
    exact List.mem_append_left _ (List.mem_append_left _ present)
  simpa only [current] using GeneralNominalRawSupport183.capture_inputs_separate packet high outside name

 theorem nonpoint_binder_endpoints_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (other : Nat) :
    candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).1 ∧
      candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).2 := by
  simp only [Plan.binder,input,ite_false,nonpoint,current]
  exact current_capture_separate reachable candidate.packet current (by omega) other

end Yulang.GeneralNominalHeadCandidateSupport186
