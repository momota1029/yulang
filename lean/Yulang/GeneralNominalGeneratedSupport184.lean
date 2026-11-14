import Yulang.GeneralNominalRawSupport183
import Yulang.GeneralNominalCenteredGroundBoundary

/-! Generated materialization observations retain their request source roots.
The bounds on actual request targets are separate from this structural fact. -/
namespace Yulang.GeneralNominalGeneratedSupport184
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query)
open GeneralNominalCenteredModelExtension (originSource)

def Roots (body : Schema) (names : List Nat) : Prop :=
  (∀ test ∈ body.tests, originSource test.1 ∈ names) ∧
  ∀ entry ∈ body.variables, originSource entry.origin ∈ names

theorem roots_append (one : Roots first names) (two : Roots last names) :
    Roots (first.append last) names := by
  constructor
  · intro test member
    rcases List.mem_append.mp member with member | member
    · exact one.1 test member
    · exact two.1 test member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact one.2 entry member
    · exact two.2 entry member

mutual
 theorem schema_roots (query : Query) (origin : Origin) (mode : Mode)
     (known : originSource origin ∈ names) : Roots (schema query origin mode) names := by
  cases query with
  | variables variables =>
    simp only [schema, Roots]
    refine ⟨?_,?_⟩
    · intro test member; cases member
    · intro entry member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      exact known
  | deferred id => simp [schema, Roots]
  | scalar base =>
    simp only [schema, Roots]
    refine ⟨?_,fun _ member => by cases member⟩
    intro test member
    obtain rfl := List.mem_singleton.mp member
    exact known
  | node shape children =>
    simp only [schema, Roots]
    have nested := schemas_roots children (fun index => .structural origin shape index) mode 0
      (fun _ => known)
    refine ⟨?_,nested.2⟩
    intro test member
    rcases List.mem_cons.mp member with rfl | member
    · exact known
    · exact nested.1 test member
  | nominal name children =>
    simp only [schema, Roots]
    have nested := schemas_roots children (fun index => .nominal origin name index) .actual 0
      (fun _ => known)
    refine ⟨?_,nested.2⟩
    intro test member
    rcases List.mem_cons.mp member with rfl | member
    · exact known
    · exact nested.1 test member
 termination_by sizeOf query

 theorem schemas_roots (queries : List Query) (origins : Nat → Origin) (mode : Mode) (offset : Nat)
     (known : ∀ index, originSource (origins index) ∈ names) :
     Roots (schemas queries origins mode offset) names := by
  cases queries with
  | nil => simp [schemas, Roots]
  | cons query rest =>
    simp only [schemas]
    exact roots_append (schema_roots query (origins offset) mode (known offset))
      (schemas_roots rest origins mode (offset+1) known)
 termination_by sizeOf queries
end

theorem roots_mono (supported : Roots body first) (included : first ⊆ last) : Roots body last :=
  ⟨fun test member => included (supported.1 test member),
   fun entry member => included (supported.2 entry member)⟩

theorem generated_roots (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) :
    Roots (generated state interpretation requests) (requests.map Request.target) := by
  induction requests with
  | nil => simp [generated, Roots]
  | cons request rest ih =>
    simp only [generated, List.map_cons, List.foldr_cons]
    change Roots ((schema _ _ _).append (generated state interpretation rest)) _
    apply roots_append
    · exact schema_roots _ _ _ (List.mem_cons_self ..)
    · exact roots_mono ih (fun _ member => List.mem_cons_of_mem _ member)

open GeneralDeclarations GeneralDeclarationDemands

theorem input_request_target (input : InputRequest) (request : Request)
    (member : request ∈ inputRequests input) :
    request.target = input.endpoints.1 ∨ request.target = input.endpoints.2 := by
  unfold inputRequests at member
  split at member
  · cases member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem emitted_target_separate (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (ins : ∀ name, fresh ≠ (capture.inputs name).1 ∧ fresh ≠ (capture.inputs name).2)
    (outs : ∀ name, fresh ≠ capture.outputs name)
    (args : ∀ index, fresh ≠ (allocation.arguments index).1 ∧ fresh ≠ (allocation.arguments index).2)
    (allocated : ∀ name, fresh ≠ allocation.outputs name)
    (request : Request) (member : request ∈ emissionRequests (emit invocation declaration clause valid capture allocation)) :
    fresh ≠ request.target := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨input,present,requested⟩ := List.mem_flatMap.mp member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    have endpoints : fresh ≠ ((childDemand declaration clause valid capture allocation).arguments index).1 ∧
        fresh ≠ ((childDemand declaration clause valid capture allocation).arguments index).2 := by
      dsimp only [childDemand]
      unfold inputInterval
      split
      · exact ins _
      · exact args index
    rcases input_request_target _ request requested with equal | equal
    · exact fun collision => endpoints.1 (collision.trans equal)
    · exact fun collision => endpoints.2 (collision.trans equal)
  · obtain ⟨output,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨equation,_,rfl⟩ := List.mem_map.mp present
    unfold outputTarget
    split
    · split
      · exact outs _
      · exact allocated _
    · exact allocated _

theorem root_request_target (declaration : Declaration) (root : GeneralSourceDictionaries.Occurrence roles)
    (request : Request) (member : request ∈ rootRequests declaration root) :
    ∃ output ∈ root.demand.outputs, request.target = output.target := by
  obtain ⟨output,present,member⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,_,rfl⟩ := List.mem_map.mp member
  exact ⟨output,present,rfl⟩

open GeneralNominalCenters (fresh)

theorem packet_request_separate (packet : GeneralNominalSaturationState.Packet roles)
    (linked : GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (request : Request)
    (member : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠ request.target := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨output,present,equal⟩ := root_request_target _ _ request member
    exact fun collision => outside ((collision.trans equal).symm ▸ linked.2 output present)
  · obtain ⟨emission,present,member⟩ := List.mem_flatMap.mp member
    have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
      packet.declaration packet.checked _ _).mem_iff.mpr present
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp old
    apply emitted_target_separate _ _ _ _ _ _ _ _ _ request member
    · exact GeneralNominalRawSupport183.capture_inputs_separate packet high outside
    · exact GeneralNominalRawSupport183.capture_output_separate packet high
    · intro index
      exact ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3),
        GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4)⟩
    · intro name
      exact GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 5)

theorem packet_generated_separate (packet : GeneralNominalSaturationState.Packet roles)
    (linked : GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds) := by
  intro member
  have roots := generated_roots packet.context.state packet.context.interpretation
    (requests packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings)
  have excluded (name) (listed : name ∈ (requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings).map Request.target) :
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ name := by
    obtain ⟨request,present,rfl⟩ := List.mem_map.mp listed
    exact packet_request_separate packet linked high outside request present
  rcases List.mem_append.mp member with member | member
  · obtain ⟨test,present,equal⟩ := List.mem_map.mp member
    exact excluded _ (roots.1 test present) equal.symm
  · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp member
    simp only [GeneralNominalRawFrame179.useSources, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal | equal
    · exact excluded _ (roots.2 entry present) equal
    · exact GeneralNominalRawSupport183.capture_output_separate packet high entry.name equal
    · exact (GeneralNominalRawSupport183.capture_inputs_separate packet high outside entry.name).1 equal
    · exact (GeneralNominalRawSupport183.capture_inputs_separate packet high outside entry.name).2 equal

open GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAncestry (InstalledDepthBound)

 theorem packet_linked
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus next action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨_,_,_,_,_,_,prepared,_,_,_,_,_⟩ := enabled.1
        exact prepared.2.1
      · exact ih packet member

theorem historical_generated_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds) := by
  have seed := GeneralNominalRawSupport183.packet_seed path packet member
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [seed]
    exact fun present => GeneralNominalCenteredAllocation.outside_pool source high
      (GeneralNominalRawOrigin182.packet_context_pool source bound path packet member present)
  simpa only [seed] using packet_generated_separate packet (packet_linked path packet member) high outside

theorem ground_generated_separate
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds) := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(GeneralNominalCenteredTrace.configuration_trace path).1]
  exact historical_generated_separate source
    (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path packet member high

theorem historical_packet_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet := by
  intro present
  rcases List.mem_append.mp present with present | present
  · rcases List.mem_append.mp present with present | present
    · exact GeneralNominalRawSupport183.historical_private_separate source bound path packet member high present
    · exact GeneralNominalRawOrigin182.fresh_outside_packet_report source bound path packet member high present
  · exact historical_generated_separate source bound path packet member high present

theorem ground_packet_separate
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(GeneralNominalCenteredTrace.configuration_trace path).1]
  exact historical_packet_separate source
    (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path packet member high

end Yulang.GeneralNominalGeneratedSupport184
