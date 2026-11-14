import Yulang.GeneralNominalChildCoherence184
import Yulang.GeneralNominalGroundProvenance182
import Yulang.GeneralNominalCenteredWhere

/-! Equal occurrences in an actual centered trace have equal center sites.
No semantic agreement premise is used; checked declaration IDs and deterministic
child allocation recover the producer. -/
namespace Yulang.GeneralNominalGroundSiteCoherence184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem registered_producers
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    (∀ site ∈ state.sites, root.identity ≤ site.occurrence.identity) ∧
    (∀ plan ∈ state.plans, root.identity ≤ plan.packet.site.occurrence.identity ∧
      plan.packet.declaration ∈ registry.declarations) := by
  induction path with
  | refl =>
    refine ⟨?_,?_⟩
    · intro site member
      cases List.mem_singleton.mp member
      exact Nat.le_refl _
    · intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      have parent : root.identity ≤ plan.packet.site.occurrence.identity := by
        rw [← plan.input_exact]
        exact ih.1 plan.input guard.1
      refine ⟨?_,?_⟩
      · intro site member
        rcases List.mem_append.mp member with old | added
        · exact ih.1 site old
        · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
          have child := GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
            (plan.packet.checked.signature.2.2.2 clause.val clause.property)
          exact Nat.le_trans parent (Nat.le_of_lt (GeneralNominalCenteredWhere.packet_child_above plan.packet _ child))
      · intro historical member
        rcases List.mem_cons.mp member with rfl | old
        · exact ⟨parent,enabled.1.2.2.2.1⟩
        · exact ih.2 historical old

theorem emitted_not_root
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (site : Site roles) (emitted : site ∈ plan.emitted) : site.occurrence ≠ root := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
  have parent := ((registered_producers path).2 plan registered).1
  have child := GeneralNominalCenteredWhere.packet_child_above plan.packet _
    (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
      (plan.packet.checked.signature.2.2.2 clause.val clause.property))
  intro same
  have equal := congrArg Occurrence.identity same
  change (GeneralNominalFeedbackSites.clauseChild plan.packet clause.val _).identity = root.identity at equal
  omega

theorem trace_site_unique (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : first.occurrence = last.occurrence) : first = last := by
  rcases GeneralNominalSiteOrigin182.initial_site_origin path first one with rfl | ⟨a,ha,ea⟩
  · rcases GeneralNominalSiteOrigin182.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
    · rfl
    · exact False.elim (emitted_not_root path b hb last eb same.symm)
  · rcases GeneralNominalSiteOrigin182.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
    · exact False.elim (emitted_not_root path a ha first ea same)
    · obtain ⟨ca,_,rfl⟩ := List.mem_map.mp ea
      obtain ⟨cb,_,rfl⟩ := List.mem_map.mp eb
      apply GeneralNominalChildCoherence184.child_site_equal registry checked a b
        ((GeneralNominalSiteOrigin182.plan_seed path a ha).trans (GeneralNominalSiteOrigin182.plan_seed path b hb).symm)
        ((registered_producers path).2 a ha).2 ((registered_producers path).2 b hb).2
        ca.val cb.val ca.property cb.property _ _ same

theorem ground_site_unique (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : first.occurrence = last.occurrence) : first = last := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact trace_site_unique checked path first last one two same

end Yulang.GeneralNominalGroundSiteCoherence184
