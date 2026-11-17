import Yulang.GeneralNominalVersionedTraceSupport237
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedTraceSiteSupport237
open GeneralNominalVersionedJournal232
open GeneralNominalCenteredFrame179 (siteSources)
open GeneralNominalVersionedTraceSupport237 (Derivation)
variable {roles : Roles.RoleDecls}
def Covered (state : State roles) (names : List Nat) : Prop :=
 ∀ site ∈ state.core.sites, siteSources site ⊆ names

theorem current (state : State roles) : Covered state (GeneralNominalVersionedJournalFrame236.sources state) := by
 intro site member n present
 have included : n ∈ state.core.sites.flatMap siteSources := List.mem_flatMap.mpr ⟨site,member,present⟩
 simp [GeneralNominalVersionedJournalFrame236.sources,
   GeneralDictionaryDefaultJournalSupport213.journalSources,included]

theorem emitted (plan : GeneralNominalCenters.Plan roles)
 (member : site ∈ GeneralNominalVersionedChildren232.emitted plan) :
 siteSources site ⊆ GeneralNominalVersionedResidualFrame237.sources plan := by
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
 have named := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
 intro n present
 have inner : n ∈ GeneralNominalVersionedResidualFrame237.childSources plan := by
   apply List.mem_flatMap.mpr
   refine ⟨⟨clause.val,named⟩,by simp,?_⟩
   exact List.mem_append_left _ present
 simp [GeneralNominalVersionedResidualFrame237.sources,inner]

theorem trace (path : Derivation before names after finalNames) (old : Covered before names) :
 Covered after finalNames := by
 induction path with
 | refl => exact old
 | observation path action ih =>
   have previous := ih old
   cases action <;> exact previous
 | merge one two path ih =>
   intro site member n present
   exact List.mem_append_left _ (ih old site member present)
 | install effect path snapshot ih =>
   intro site member n present
   change site ∈ _ ++ GeneralNominalVersionedChildren232.emitted effect.plan at member
   rcases List.mem_append.mp member with member | member
   · exact List.mem_append_left _ (ih old site member present)
   · have inner := emitted effect.plan member present
     apply List.mem_append_right
     simp [GeneralNominalVersionedResidualSupportSteps237.installSources,inner]

theorem source (path : GeneralNominalVersionedTraceSupport237.Reachable registry root state) :
 ∃ names, GeneralNominalVersionedModelSupport237.Support state names ∧ Covered state names := by
 obtain ⟨initial,names,_,derived,supported⟩ := GeneralNominalVersionedTraceSupport237.source path
 exact ⟨names,supported,trace derived (current initial)⟩
end Yulang.GeneralNominalVersionedTraceSiteSupport237
