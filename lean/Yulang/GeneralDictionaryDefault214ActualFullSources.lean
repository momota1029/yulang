import Yulang.GeneralDictionaryDefault214ActualTotalSources
import Yulang.GeneralDictionaryDefaultJournalSupport213

/-! Every purpose-eight source of the complete reservation-free213 journal
has a historical binder producer. This includes raw total-expression reads;
producer identity does not assert declaredness or actual-origin readback. -/
namespace Yulang.GeneralDictionaryDefault214ActualFullSources
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefault214ActualTotalSources
open GeneralDictionaryDefault214ActualSupport
open GeneralDictionaryDefault214ActualEffects (effect_plan_registered effect_snapshot)
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultModeSupport213 (schemaSources)
open GeneralDictionaryDefaultTotalFrame212 (resolve bodyResolve)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

 theorem raw_body_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (separate : fresh context.state.seed invocation declaration 8 owner position ≠ target)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultModeEffects213.bodySources plan target body) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   unfold GeneralDictionaryDefaultModeEffects213.bodySources schemaSources bodySchema at member
   cases compiled : compileBody plan body with
   | none => simp [compiled] at member
   | some expression =>
       simp only [compiled,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_cons] at member
       rcases member with equal | read
       · exact False.elim (separate equal)
       · obtain ⟨mode,name,equal⟩ := reads_source _ _ _ read
         cases body with
         | explicit equation => exact resolved_binder source bound path plan registered equal
         | default role output term =>
             have centerMember : fresh context.state.seed invocation declaration 8 owner position ∈ List.ofFn plan.input.center ++ [0] := by
               change (List.ofFn plan.input.center)[name]?.getD 0 = _ at equal
               cases found : (List.ofFn plan.input.center)[name]? with
               | none =>
                   simp only [found,Option.getD_none] at equal
                   rw [← equal]
                   exact List.mem_append_right _ (List.mem_singleton_self _)
               | some identity =>
                   simp only [found,Option.getD_some] at equal
                   rw [← equal]
                   exact List.mem_append_left _ (List.mem_of_getElem? found)
             obtain ⟨origin,producer⟩ := center_list_actual source path plan.input (registered_input path plan registered) centerMember
             exact actual_binder producer

 theorem raw_class_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (separate : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests view focus,
       fresh context.state.seed invocation declaration 8 owner position ≠ output.target)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultModeEffects213.classSources view focus plan) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp member
   rcases List.mem_cons.mp within with equal | within
   · exact False.elim (separate output requested equal)
   · obtain ⟨body,_,within⟩ := List.mem_flatMap.mp within
     exact raw_body_binder source bound path plan registered (separate output requested) within

 theorem packet_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (plan : Plan roles) (registered : plan ∈ state.core.plans)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultPacketSupport213.packetSources plan) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   simp only [GeneralDictionaryDefaultPacketSupport213.packetSources,List.mem_append] at member
   rcases member with ((((head | input) | captures) | schema) | emitted) | child
   · exact False.elim (GeneralDictionaryDefaultRawSeparation213.historical_head_separate source bound path plan
       (registered_packets path plan registered) (by decide) head)
   · obtain ⟨origin,producer⟩ := site_support_actual source bound path plan.input (registered_input path plan registered) input
     exact actual_binder producer
   · obtain ⟨origin,producer⟩ := capture_support_actual source bound path plan registered captures
     exact actual_binder producer
   · obtain ⟨origin,producer⟩ := head_support_actual source bound path plan registered schema
     exact actual_binder producer
   · exact emitted_schema_binder source bound path plan registered emitted
   · obtain ⟨clause,_,within⟩ := List.mem_flatMap.mp child
     rcases List.mem_append.mp within with site | schema
     · have present : plan.childSite clause.val _ ∈ state.core.sites :=
         registered_emitted path plan registered _ (List.mem_map.mpr ⟨clause,List.mem_attach ..,rfl⟩)
       obtain ⟨origin,producer⟩ := site_support_actual source bound path _ present site
       exact actual_binder producer
     · exact child_schema_binder source bound path plan registered clause.val clause.property _ schema

 theorem raw_effect_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (effect : Effect roles) (registered : effect ∈ state.effects)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultJournalSupport213.effectSources state effect) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   rcases List.mem_append.mp member with member | live
   · rcases List.mem_append.mp member with head | snapshot
     · obtain ⟨origin,producer⟩ := GeneralDictionaryDefault214ActualJournal.head_support_actual source bound path
         effect.plan (effect_plan_registered path effect registered) head
       exact actual_binder producer
     · obtain ⟨before,prior,snapshotEq⟩ := effect_snapshot path effect registered
       apply raw_class_binder source bound path effect.plan (effect_plan_registered path effect registered) _ snapshot
       intro output requested
       rw [snapshotEq] at requested
       exact GeneralDictionaryDefault214ActualEffects.request_separate source bound prior requested (by decide)
   · apply raw_class_binder source bound path effect.plan (effect_plan_registered path effect registered) _ live
     intro output requested
     exact GeneralDictionaryDefault214ActualEffects.request_separate source bound path requested (by decide)

 theorem observed_subset (site : Site roles) :
     GeneralNominalCenteredEmptyFrame179.rawSiteSources site.observed ⊆ GeneralNominalCenteredFrame179.siteSources site := by
   intro name member
   rcases List.mem_append.mp member with endpoint | origin
   · obtain ⟨pair,present,within⟩ := List.mem_flatten.mp endpoint
     obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
     apply List.mem_flatten.mpr
     refine ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,?_⟩
     simp only [List.mem_cons,List.not_mem_nil,or_false] at within ⊢
     exact within.elim Or.inl (fun h => Or.inr (Or.inl h))
   · obtain ⟨origin,present,equal⟩ := List.mem_map.mp origin
     obtain ⟨observed,within,found⟩ := List.mem_filterMap.mp present
     obtain ⟨index,rfl⟩ := List.mem_ofFn.mp within
     cases Option.some.inj found
     apply List.mem_flatten.mpr
     refine ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,?_⟩
     simp only [GeneralNominalCenteredModelExtension.originSource] at equal
     simp [equal]

 theorem raw_site_origin
     (path : B4Target.Steps (Step registry root) (initial context root) state) :
     ∀ raw ∈ state.core.erased.current.sites, raw = GeneralNominalDemandMerging.pointSite root ∨
       ∃ site ∈ state.core.sites, raw = site.observed := by
   induction path with
   | refl => intro raw member; exact Or.inl (List.mem_singleton.mp member)
   | @tail before after path step ih =>
       obtain ⟨focus,generated,action⟩ := step
       cases action with
       | administrative action =>
           cases action with
           | enqueue linked absent =>
               obtain ⟨site,member,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                 (GeneralDictionaryDefaultTrace208.registered_trace path) generated
               exact False.elim (absent site member same)
           | refresh | equate | reobserve => exact ih
       | refresh | merge => exact ih
       | install effect enabled novel =>
           intro raw member
           rcases List.mem_append.mp member with old | added
           · rcases ih raw old with initial | ⟨site,present,equal⟩
             · exact Or.inl initial
             · exact Or.inr ⟨site,List.mem_append_left _ present,equal⟩
           · obtain ⟨site,present,equal⟩ := List.mem_map.mp added
             exact Or.inr ⟨site,List.mem_append_right _ present,equal.symm⟩

 theorem original_context
     (path : B4Target.Steps (Step registry root) (initial context root) state) :
     state.core.erased.source = context := by
   induction path with
   | refl => rfl
   | tail path step ih =>
       obtain ⟨focus,_,action⟩ := step
       cases action with
       | administrative action => cases action <;> exact ih
       | refresh | merge | install => exact ih

 theorem full_support_binder
     (source : GeneralNominalSourceFormation.InitialSource registry context root)
     (bound : InstalledDepthBound registry context root limit)
     (path : B4Target.Steps (Step registry root) (initial context root) state)
     (member : fresh context.state.seed invocation declaration 8 owner position ∈
       GeneralDictionaryDefaultJournalSupport213.journalSources state) :
     BinderProducer state (fresh context.state.seed invocation declaration 8 owner position) := by
   simp only [GeneralDictionaryDefaultJournalSupport213.journalSources,List.mem_append] at member
   rcases member with ((((current | original) | raw) | sites) | plans) | effects
   · exact False.elim (GeneralDictionaryDefaultRawSeparation213.current_separate source bound path (by decide)
       (GeneralDictionaryDefaultRawSupport213.subset _ current))
   · rw [original_context path] at original
     have present := GeneralDictionaryDefaultRawSupport213.subset _ original
     exact False.elim (GeneralNominalCenteredAllocation.outside_pool (limit := limit) source (by decide : 7 ≤ 8)
       (List.mem_append_left _ present))
   · obtain ⟨raw,registered,within⟩ := List.mem_flatMap.mp raw
     rcases raw_site_origin path raw registered with rfl | ⟨site,siteRegistered,rfl⟩
     · have present := GeneralNominalSiteSupport184.point_sources root source.linked.1 within
       exact False.elim (GeneralNominalCenteredAllocation.outside_pool (limit := limit) source (by decide : 7 ≤ 8)
         (List.mem_append_left _ present))
     · obtain ⟨origin,producer⟩ := site_support_actual source bound path site siteRegistered (observed_subset site within)
       exact actual_binder producer
   · obtain ⟨site,registered,within⟩ := List.mem_flatMap.mp sites
     obtain ⟨origin,producer⟩ := site_support_actual source bound path site registered within
     exact actual_binder producer
   · obtain ⟨plan,registered,within⟩ := List.mem_flatMap.mp plans
     exact packet_binder source bound path plan registered within
   · obtain ⟨effect,registered,within⟩ := List.mem_flatMap.mp effects
     exact raw_effect_binder source bound path effect registered within

end Yulang.GeneralDictionaryDefault214ActualFullSources
