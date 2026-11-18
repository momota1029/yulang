import Yulang.GeneralRebaseRegisteredPlan263
import Yulang.GeneralNominalChildSemantic186
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegisteredSites263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

/-- The actual input site of every retained versioned plan is retained. -/
theorem inputs (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (state : State roles)
 (path : B4Target.Steps (Step registry root) (initial context root) state) :
 ∀ plan ∈ state.plans, plan.input ∈ state.core.sites := by
 induction path with
 | refl => intro plan member; cases member
 | @tail before after path step ih =>
   have growth := GeneralNominalVersionedMixedGrowth234.step step
   obtain ⟨focus,generated,action⟩ := step
   cases action with
   | administrative action => cases action <;> exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro plan member
     rcases List.mem_cons.mp member with rfl | prior
     · exact List.mem_append_left _ (GeneralNominalVersionedMixedAncestry237.frame enabled).center_recorded
     · exact List.mem_append_left _ (ih plan prior)

/-- All centered sites come from the one initial site or an actual retained
versioned producer. Administrative enqueue cannot add a centered site. -/
theorem origin (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (state : State roles)
 (path : B4Target.Steps (Step registry root) (initial context root) state) :
 ∀ site ∈ state.core.sites,
 site = rootSite context.state.seed root ∨
 ∃ plan ∈ state.plans, site ∈ GeneralNominalVersionedChildren232.emitted plan := by
 induction path with
 | refl => intro site member; exact Or.inl (List.mem_singleton.mp member)
 | @tail before after path step ih =>
   obtain ⟨focus,generated,action⟩ := step
   cases action with
   | administrative action =>
     cases action with
     | enqueue linked absent =>
       obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
         (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
       exact False.elim (absent site member same)
     | refresh | equate | reobserve => exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro site member
     rcases List.mem_append.mp member with prior | added
     · rcases ih site prior with initial | ⟨plan,present,emitted⟩
       · exact Or.inl initial
       · exact Or.inr ⟨plan,List.mem_cons_of_mem _ present,emitted⟩
     · exact Or.inr ⟨effect.plan,List.mem_cons_self,added⟩


/-- Numeric invocation identities strictly grow along emitted ancestry. -/
theorem above_root (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (state : State roles)
 (path : B4Target.Steps (Step registry root) (initial context root) state) :
 ∀ site ∈ state.core.sites, root.identity ≤ site.occurrence.identity := by
 induction path with
 | refl => intro site member; cases List.mem_singleton.mp member; exact Nat.le_refl _
 | @tail before after path step ih =>
   obtain ⟨focus,generated,action⟩ := step
   cases action with
   | administrative action =>
     cases action with
     | enqueue linked absent =>
       obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
         (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
       exact False.elim (absent site member same)
     | refresh | equate | reobserve => exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro site member
     rcases List.mem_append.mp member with prior | added
     · exact ih site prior
     · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
       have parent := ih effect.plan.input (GeneralNominalVersionedMixedAncestry237.frame enabled).center_recorded
       have present := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
       have child := GeneralNominalCenteredWhere.packet_child_above effect.plan.packet _
         (GeneralNominalCenteredTrace.clauseChild_mem effect.plan.packet clause.val present
           (effect.plan.packet.checked.signature.2.2.2 clause.val present))
       rw [effect.plan.input_exact] at parent
       exact Nat.le_trans parent (Nat.le_of_lt child)

theorem emitted_above_root (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (state : State roles)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (plan : Plan roles) (member : plan ∈ state.plans)
 (site : Site roles) (emitted : site ∈ GeneralNominalVersionedChildren232.emitted plan) :
 root.identity < site.occurrence.identity := by
 have parent := above_root registry context root state path plan.input (inputs registry context root state path plan member)
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
 have present := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
 have child := GeneralNominalCenteredWhere.packet_child_above plan.packet _
   (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val present
     (plan.packet.checked.signature.2.2.2 clause.val present))
 rw [plan.input_exact] at parent
 exact Nat.lt_of_le_of_lt parent child
end Yulang.GeneralRebaseRegisteredSites263
