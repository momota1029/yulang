import Yulang.GeneralNominalVersionedTraceSiteSupport237
import Yulang.GeneralNominalVersionedSupportedActual237
import Yulang.GeneralDictionaryDefault214ActualSupport
import Yulang.GeneralDictionaryHeadSharing220
set_option backward.isDefEq.respectTransparency false
/-! The actual current head survives selective aggregate realization. No Fresh,
coverage, sharing witness, or satisfiability premise is needed for preservation. -/
namespace Yulang.GeneralNominalVersionedSupportedHead237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedSupportedCompletion237 (extended preserves)
open GeneralNominalVersionedSupportedCompletion237 (pool)
open GeneralNominalCenteredModelExtension (originSource)
variable (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)

theorem zero_kept : extended names state plan model 0 = model 0 := by
  apply GeneralNominalSelectiveEquationRealization236.outside
  intro entry member
  obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  all_goals
    have p0 := GeneralNominalAggregateVersion231.above_seed plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 0 name plan.packet.bindings
    have p1 := GeneralNominalAggregateVersion231.above_seed plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 1 name plan.packet.bindings
    dsimp only [Prod.fst]
    omega

variable (covered : GeneralNominalVersionedTraceSiteSupport237.Covered state names)
include covered

theorem registered_site (site : Site roles) (registered : site ∈ state.core.sites)
    (identity) (member : identity ∈ GeneralNominalCenteredFrame179.siteSources site) :
    extended names state plan model identity = model identity := by
  apply preserves
  exact List.mem_append_left _ (List.mem_append_left _ (covered site registered member))

theorem center_kept (registered : plan.input ∈ state.core.sites) (index) :
    extended names state plan model (plan.input.center index) = model (plan.input.center index) := by
  apply registered_site names state plan model covered plan.input registered
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem root_kept (registered : plan.input ∈ state.core.sites) (identity)
    (member : identity ∈ List.ofFn plan.input.center ++ [0]) :
    extended names state plan model identity = model identity := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact center_kept names state plan model covered registered index
  · cases List.mem_singleton.mp member
    exact zero_kept names state plan model

theorem head_schema_iff (registered : plan.input ∈ state.core.sites) :
    GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema (extended names state plan model) ↔
      GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model := by
  apply GeneralNominalVersionedHeadFrame236.schema_iff
  intro identity member
  rcases List.mem_append.mp member with testMember | used
  · obtain ⟨test,present,rfl⟩ := List.mem_map.mp testMember
    exact root_kept names state plan model covered registered _
      ((GeneralDictionaryDefault214ActualSupport.head_roots plan).1 test present)
  · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp used
    have actual := GeneralNominalHeadSchemaNames186.head_actual plan entry present
    simp only [GeneralNominalVersionedHeadFrame236.variableSources,actual,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact root_kept names state plan model covered registered _
        ((GeneralDictionaryDefault214ActualSupport.head_roots plan).2 entry present)
    · exact GeneralNominalVersionedSupportedActual237.binder_kept names state plan model entry.name

theorem sharing_iff (registered : plan.input ∈ state.core.sites) :
    GeneralDictionaryHeadSharing220.Holds plan (extended names state plan model) ↔
      GeneralDictionaryHeadSharing220.Holds plan model := by
  rw [GeneralDictionaryHeadSharing220.holds_iff,GeneralDictionaryHeadSharing220.holds_iff]
  apply forall_congr'; intro first
  apply forall_congr'; intro one
  apply forall_congr'; intro last
  apply forall_congr'; intro two
  apply forall_congr'; intro _
  exact GeneralNominalCenteredFrame179.same_iff _ _
    (root_kept names state plan model covered registered _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).2 first one))
    (root_kept names state plan model covered registered _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).2 last two))
end Yulang.GeneralNominalVersionedSupportedHead237
