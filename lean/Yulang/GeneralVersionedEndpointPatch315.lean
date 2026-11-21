import Yulang.GeneralVersionedHighJournal315

set_option backward.isDefEq.respectTransparency false
/-! A proposed new endpoint cell can receive its RHS in one assignment
without perturbing the *existing* source journal or the current head and
class equations. This is allocator isolation, not operational soundness
for a changed child demand. -/
namespace Yulang.GeneralVersionedEndpointPatch315
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedTraceDomain313 (seed raw context)
open GeneralNominalIdentities (Origin source source_above_seed)
open GeneralVersionedHighOrigins315 (Absent raw_absent input_domain binder_domain)
open GeneralVersionedHighJournal315 (patch patch_preserves)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralVersionedEndpointAddress315 (Side atCell key footprint)
open GeneralNominalVersionedExpressionFrame236 (reads variableSource variable_value value_eq)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open CommonNominalFullCarrier (Ty)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCenteredFrame179 (Agree siteSources)

theorem aligned_domain {s : State roles} {p : Plan roles} (aligned : p.packet.context = context s) :
    p.packet.context.state.seed = seed s ∧ GeneralNominalState.sources p.packet.context.state ⊆ raw s := by
  rw [aligned]
  exact ⟨rfl,fun _ h => h⟩

theorem operand_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (aligned : p.packet.context = context s) (tag : 9 < k.2.2.1)
    (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    Absent s k (variableSource p mode name) := by
  obtain ⟨seedEq,domain⟩ := aligned_domain aligned
  unfold variableSource
  split
  · exact binder_domain actual seedEq domain tag name
  · cases mode
    · exact (input_domain actual seedEq domain tag name).1
    · exact (input_domain actual seedEq domain tag name).2
    · exact binder_domain actual seedEq domain tag name

theorem body_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : 9 < k.2.2.1)
    (aligned : p.packet.context = context s) (recorded : p.input ∈ s.core.sites)
    (target : Nat) (allowed : Absent s k target) (body : GeneralDictionaryAssociatedProvenance.Body) :
    ∀ n ∈ bodySources p target body, Absent s k n := by
  obtain ⟨seedEq,domain⟩ := aligned_domain aligned
  intro n member
  cases body with
  | explicit eq =>
    rcases List.mem_cons.mp member with rfl|later
    · exact allowed
    · obtain ⟨name,_,rfl⟩ := List.mem_map.mp later
      rw [← GeneralNominalVersionedFrame231.binder_eq]
      exact binder_domain actual seedEq domain tag name
  | default role name term =>
    change n ∈ GeneralDictionaryDefaultModeSupport213.schemaSources
      (GeneralDictionaryDefaultTotalFrame212.bodyResolve p (.default role name term))
      (GeneralNominalCenteredHeadMatEffects.bodySchema p target (.default role name term)) at member
    unfold GeneralNominalCenteredHeadMatEffects.bodySchema at member
    split at member
    · obtain ⟨eq,he,inside⟩ := List.mem_flatMap.mp member
      cases List.mem_singleton.mp he
      rcases List.mem_cons.mp inside with rfl|read
      · exact allowed
      · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at read
        obtain ⟨index,_,rfl⟩ := List.mem_map.mp read
        exact GeneralVersionedHighClass315.default_origin actual tag recorded index
    · cases member

theorem classes_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : 9 < k.2.2.1)
    (frame : Frame (Compiled registry) s.core focus keyId p) :
    ∀ n ∈ classSources s.core p.packet.site.occurrence p, Absent s k n := by
  intro n observed
  obtain ⟨rq,found,within⟩ := List.mem_flatMap.mp observed
  obtain ⟨site,registered,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp found
  have target := GeneralVersionedHighPacket315.outputs_ne actual tag site registered rq requested
  rcases List.mem_cons.mp within with rfl|inside
  · exact target
  · obtain ⟨body,_,read⟩ := List.mem_flatMap.mp inside
    exact body_absent actual tag frame.context_eq frame.center_recorded rq.target target body _ read

theorem head_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : 9 < k.2.2.1)
    (frame : Frame (Compiled registry) s.core focus keyId p) :
    ∀ n ∈ GeneralNominalVersionedResidualFrame237.headSources p.packet, Absent s k n := by
  intro n member hit
  have visible : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq ▸ frame.visible
  rcases List.mem_append.mp member with atoms|report
  · rcases List.mem_append.mp (GeneralVersionedInstallDomain313.head_sources p.packet visible atoms) with current|reserve
    · rw [frame.context_eq,hit] at current
      exact raw_absent actual tag current
    · have eq := (aligned_domain frame.context_eq).1
      rw [hit,← eq] at reserve
      have bound := GeneralVersionedInstallDomain313.reserve_purpose p.packet reserve
      omega
  · have current := GeneralVersionedRawReportDomain313.raw_membership p.packet report
    rw [frame.context_eq,hit] at current
    exact raw_absent actual tag current

theorem schema_absent {s : State roles} {p : Plan roles} {k : Origin}
    (actual : Reachable registry root s) (tag : 9 < k.2.2.1)
    (frame : Frame (Compiled registry) s.core focus keyId p) :
    ∀ n ∈ GeneralNominalVersionedHeadFrame236.schemaSources p p.headSchema, Absent s k n := by
  obtain ⟨seedEq,domain⟩ := aligned_domain frame.context_eq
  have observed : ∀ n ∈ GeneralVersionedHeadFromSharing313.origins p, Absent s k n := by
    apply GeneralVersionedSchemaOrigins313.centers p (Absent s k)
    · intro hit
      have above := source_above_seed (seed s) k
      omega
    · intro i
      exact GeneralVersionedHighPacket315.registered actual tag p.input frame.center_recorded _
        (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩)
  intro n listed
  rcases List.mem_append.mp listed with test|binderUse
  · exact observed n (List.mem_append_left _ test)
  · obtain ⟨use,seen,inside⟩ := List.mem_flatMap.mp binderUse
    have tagUse := GeneralNominalHeadSchemaNames186.head_actual p use seen
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,tagUse,ite_true,List.mem_cons,
      List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl
    · exact observed _ (List.mem_append_right _ (List.mem_map.mpr ⟨use,seen,rfl⟩))
    · exact binder_domain actual seedEq domain tag _

theorem sound_write {s : State roles} {e : Effect roles} {m : Assignment}
    (actual : Reachable registry root s)
    (rg : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (before : GeneralVersionedChildEndpointCut315.BaseReady s e m)
    (side : Side) (clause pos : Nat) (expr : Expr) :
    let id := atCell e.plan side clause pos expr
    let n := patch m id (value (variables e.plan m) side.mode expr)
    GeneralVersionedChildEndpointCut315.BaseReady s e n ∧
      (n id).1 = value (variables e.plan n) side.mode expr := by
  let plan := e.plan
  have f : Frame (Compiled registry) s.core plan.packet.site.occurrence plan.packet.declaration.id plan :=
    rg ▸ snapshot ▸ e.frame
  let k := key plan side clause pos expr
  let id := atCell plan side clause pos expr
  have address : id = source (seed s) k := by
    change source plan.packet.context.state.seed k = _
    rw [f.context_eq]
  have tag : 9 < k.2.2.1 := by
    change 9 < side.purpose
    cases side <;> decide
  let rhs := value (variables plan m) side.mode expr
  let n := patch m id rhs
  have preserved (z : Nat) (outside : Absent s k z) : m z = n z := by
    have distinct : z ≠ id := by rwa [address]
    simp [n,patch,distinct]
  have valid : Models s n := by
    change Models s (patch m id rhs)
    rw [address,patch_preserves actual tag]
    exact before.1
  have raw₀ : GeneralNominalState.Models plan.packet.context.state m := f.context_eq.symm ▸ before.1.1.1
  have raw₁ : GeneralNominalState.Models plan.packet.context.state n := f.context_eq.symm ▸ valid.1.1
  have head := (GeneralNominalVersionedResidualFrame237.head_models_iff plan.packet raw₀ raw₁
    (fun z seen => preserved z (head_absent actual tag f z seen))).mp before.2.1
  have schema := (GeneralNominalVersionedHeadFrame236.schema_iff plan plan.headSchema
    (fun z seen => preserved z (schema_absent actual tag f z seen))).mp before.2.2.1
  have classEq := (GeneralNominalVersionedJournalFrame236.class_iff s.core plan.packet.site.occurrence plan
    (fun z seen => preserved z (classes_absent actual tag f z seen))).mp before.2.2.2
  have valueSame : rhs = value (variables plan n) side.mode expr := by
    apply value_eq
    intro r found
    simp only [variable_value]
    exact congrArg Prod.fst (preserved _ (operand_absent actual f.context_eq tag r.1 r.2))
  change _ ∧ (n id).1 = _
  exact ⟨⟨valid,head,schema,classEq⟩,by simp only [n,patch,ite_true]; exact valueSame⟩

end Yulang.GeneralVersionedEndpointPatch315
