import Yulang.GeneralDictionaryDefault214ActualJournal

/-! Raw total-expression supports retain all binder reads, including hidden
unscoped fields. For namespace freshness a historical binder producer suffices;
no claim of semantic head-origin readback is made for an undeclared binder. -/
namespace Yulang.GeneralDictionaryDefault214ActualTotalSources
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound frame)
open GeneralDictionaryDefault214ActualSupport (registered_packets registered_input registered_emitted)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode Request)
open GeneralDictionaryDefaultModeSupport212 (reads readMany)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

 def BinderProducer (state : State roles) (identity : Nat) : Prop :=
   ∃ plan ∈ state.core.plans, ∃ name, plan.binder name = identity

 theorem actual_binder (producer : GeneralDictionaryDefault214ActualReadback.Actual state identity origin) :
     BinderProducer state identity := by
   obtain ⟨plan,registered,entry,_,_,equal,_⟩ := producer
   exact ⟨plan,registered,entry.name,equal⟩

 mutual
 theorem reads_source (resolver : Mode → Nat → Nat) (mode : Mode) (expression : Expr)
     (member : identity ∈ reads resolver mode expression) : ∃ mode name, resolver mode name = identity := by
   cases expression with
   | «variable» name => exact ⟨mode,name,(List.mem_singleton.mp member).symm⟩
   | primitive _ expressions => exact many_source resolver mode expressions member
   | nominal _ expressions => exact many_source resolver .actual expressions member
   | record _ one two | join one two =>
       rcases List.mem_append.mp member with left | right
       · exact reads_source resolver mode one left
       · exact reads_source resolver mode two right
   | variant _ expression => exact reads_source resolver mode expression member
 theorem many_source (resolver : Mode → Nat → Nat) (mode : Mode) (expressions : List Expr)
     (member : identity ∈ readMany resolver mode expressions) : ∃ mode name, resolver mode name = identity := by
   cases expressions with
   | nil => cases member
   | cons head tail =>
       rcases List.mem_append.mp member with left | right
       · exact reads_source resolver mode head left
       · exact many_source resolver mode tail right
 end

 theorem resolved_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (equal : resolve plan mode name = fresh context.state.seed invocation declaration 8 owner position) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   by_cases output : name ∈ plan.packet.declaration.outputNames
   · exact ⟨plan,registered,name,by simpa only [resolve,output,ite_true] using equal⟩
   · have separate := GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
       (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
       source bound path plan.packet (registered_packets path plan registered) (by decide : 7 ≤ 8) name
     cases mode with
     | actual => exact ⟨plan,registered,name,by simpa only [resolve,output,ite_false] using equal⟩
     | lower => exact False.elim (separate.2.1 (by simpa only [resolve,output,ite_false] using equal.symm))
     | upper => exact False.elim (separate.2.2 (by simpa only [resolve,output,ite_false] using equal.symm))

 theorem total_schema_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (targets : ∀ equation ∈ schema.equations,
       equation.target = fresh context.state.seed invocation declaration 8 owner position →
       BinderProducer state (fresh context.state.seed invocation declaration 8 owner position))
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan) schema) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   obtain ⟨equation,present,within⟩ := List.mem_flatMap.mp member
   rcases List.mem_cons.mp within with target | read
   · exact targets equation present target.symm
   · obtain ⟨mode,name,equal⟩ := reads_source _ _ _ read
     exact resolved_binder source bound path plan registered equal

 theorem generated_target
     (member : equation ∈ (GeneralNominalCenteredHeadMatSchemas.generated catalogue interpretation requests).equations) :
     ∃ request ∈ requests, equation.target = request.target := by
   induction requests with
   | nil => cases member
   | cons first rest ih =>
       rcases List.mem_append.mp member with initial | later
       · unfold GeneralNominalCenteredHeadMatSchemas.materialize at initial
         split at initial
         next expression compiled =>
           cases List.mem_singleton.mp initial
           exact ⟨first,List.mem_cons_self ..,rfl⟩
         next => cases initial
       · obtain ⟨request,present,equal⟩ := ih later
         exact ⟨request,List.mem_cons_of_mem _ present,equal⟩

 theorem emitted_target_separate (decl : Declaration) (clause : Clause)
     (valid : clause.Signature roles) (capture : GeneralDeclarationDemands.Capture)
     (allocation : GeneralDeclarationDemands.Allocation roles clause)
     (ins : ∀ name, identity ≠ (capture.inputs name).1 ∧ identity ≠ (capture.inputs name).2)
     (outs : ∀ name, identity ≠ capture.outputs name)
     (args : ∀ index, identity ≠ (allocation.arguments index).1 ∧ identity ≠ (allocation.arguments index).2)
     (allocated : ∀ name, identity ≠ allocation.outputs name)
     (request : Request) (member : request ∈ GeneralNominalCenteredHeadMatSchemas.emissionRequests
       (GeneralDeclarationDemands.emit invocation decl clause valid capture allocation)) : identity ≠ request.target := by
   rcases List.mem_append.mp member with member | member
   · obtain ⟨input,present,requested⟩ := List.mem_flatMap.mp member
     obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
     have endpoints : identity ≠ ((GeneralDeclarationDemands.childDemand decl clause valid capture allocation).arguments index).1 ∧
         identity ≠ ((GeneralDeclarationDemands.childDemand decl clause valid capture allocation).arguments index).2 := by
       dsimp only [GeneralDeclarationDemands.childDemand]
       unfold GeneralDeclarationDemands.inputInterval
       split
       · exact ins _
       · exact args index
     rcases List.mem_cons.mp requested with rfl | within
     · exact endpoints.1
     · cases List.mem_singleton.mp within
       exact endpoints.2
   · obtain ⟨output,present,rfl⟩ := List.mem_map.mp member
     obtain ⟨equation,_,rfl⟩ := List.mem_map.mp present
     unfold GeneralDeclarationDemands.outputTarget
     split
     · split
       · exact outs _
       · exact allocated _
     · exact allocated _

 theorem packet_outputs_pool
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state) :
     ∀ packet ∈ state.core.erased.current.packets, ∀ output ∈ packet.site.occurrence.demand.outputs,
       output.target ∈ GeneralNominalActualTraceSupport.pool registry context root limit := by
   induction path with
   | refl => intro packet member; cases member
   | @tail before after path step ih =>
       obtain ⟨focus,_,action⟩ := step
       cases action with
       | administrative action => cases action <;> exact ih
       | refresh | merge => exact ih
       | install effect enabled novel =>
           intro packet member
           rcases List.mem_cons.mp member with rfl | member
           · exact (GeneralDictionaryDefaultEnumeration208.source_pool source bound path).2
               effect.plan.packet.site (frame enabled).raw_recorded
           · exact ih packet member

 theorem request_separate
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (member : request ∈ GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
       plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings) (high : 7 ≤ purpose) :
     fresh context.state.seed invocation declaration purpose owner position ≠ request.target := by
   have packetRegistered := registered_packets path plan registered
   have seed := GeneralDictionaryDefaultRawSeparation213.packet_seed path plan.packet packetRegistered
   rcases List.mem_append.mp member with member | member
   · obtain ⟨output,present,equal⟩ := GeneralNominalGeneratedSupport184.root_request_target _ _ request member
     intro collision
     exact GeneralNominalCenteredAllocation.outside_pool source high
       ((collision.trans equal).symm ▸ packet_outputs_pool source bound path plan.packet packetRegistered output present)
   · obtain ⟨emission,present,member⟩ := List.mem_flatMap.mp member
     have old := (GeneralCanonicalChildOrder.canonicalEmit_perm plan.packet.site.occurrence.identity
       plan.packet.declaration plan.packet.checked _ _).mem_iff.mpr present
     obtain ⟨clause,_,rfl⟩ := List.mem_map.mp old
     rw [← seed]
     apply emitted_target_separate _ _ _ _ _ _ _ _ _ request member
     · intro name
       have separate := GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
         (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
         source bound path plan.packet packetRegistered high name
       simpa only [seed] using separate.2
     · intro name
       have separate := GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
         (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
         source bound path plan.packet packetRegistered high name
       simpa only [seed] using separate.1
     · intro index
       exact ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3),
         GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4)⟩
     · intro name
       exact GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 5)

 theorem emitted_schema_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan)
         (GeneralNominalCenteredHeadMatPlans.emittedSchema plan)) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   apply total_schema_binder source bound path plan registered _ member
   intro equation present equal
   obtain ⟨request,present,target⟩ := generated_target present
   exact False.elim (request_separate source bound path plan registered present (by decide) (equal.symm.trans target))

 theorem child_schema_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan)
         (GeneralNominalCenteredHeadMatPlans.childSchema plan clause signature)) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   apply total_schema_binder source bound path plan registered _ member
   intro equation within equal
   obtain ⟨request,requested,target⟩ := generated_target within
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp requested
   have registeredChild : plan.childSite clause signature ∈ state.core.sites :=
     registered_emitted path plan registered _ (List.mem_map.mpr ⟨⟨clause,present⟩,List.mem_attach ..,rfl⟩)
   obtain ⟨origin,producer,_⟩ := GeneralDictionaryDefault214ActualReadback.uniform_site_readback
     source path _ registeredChild index (target.symm.trans equal)
   have centerEqual : (plan.childSite clause signature).center index = fresh context.state.seed invocation declaration 8 owner position := target.symm.trans equal
   exact actual_binder (centerEqual ▸ producer)
end Yulang.GeneralDictionaryDefault214ActualTotalSources
