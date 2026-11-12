import Yulang.GeneralNominalSaturationSteps

/-! Every transition adds a persistent fact. A finite basis gives accessibility
without a fuel counter. Constructing that basis from source formation and
Checked is a separate obligation; finite Paterson descent alone is not such
a construction on arbitrary regular nominal states. -/
namespace Yulang.GeneralNominalSaturationProgress

noncomputable section

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalDemandMerging (Site pointSite)

variable {roles : Roles.RoleDecls} {before after start : State roles}
variable {registry : Registry} {root : Occurrence roles}
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

inductive Fact (roles : Roles.RoleDecls) where
  | site (site : Site roles)
  | constraints (packet : Packet roles)
  | edge (parent child : Occurrence roles)
  | alias (first last : Nat)
  | known (source : Nat)

def Holds (state : State roles) : Fact roles → Prop
  | .site site => site ∈ state.sites
  | .constraints packet => ∀ model, Models state model → packet.Holds model
  | .edge parent child => (parent,child) ∈ state.edges
  | .alias first last => Alias state first last
  | .known source => GeneralNominalState.Known state.context.state source

theorem monotone (growth : Extends before after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  cases fact with
  | site site => exact growth.sites site
  | constraints packet => exact fun old model valid => old model (growth.models model valid)
  | edge parent child => exact growth.edges _
  | alias first last => exact alias_monotone growth
  | known source => exact growth.known source

theorem fresh_fact (update : Step registry root before after) :
    ∃ fact : Fact roles, ¬ Holds before fact ∧ Holds after fact := by
  classical
  obtain ⟨focus,_,action⟩ := update
  cases action with
  | enqueue focus linked absent =>
      exact ⟨.site (pointSite focus),fun member => absent _ member rfl,List.mem_append_right _ (by simp)⟩
  | install packet emitted ready novel =>
      by_cases entailed : ∀ model, Models before model → packet.Holds model
      · have missing : ∃ child ∈ packet.children, (packet.site.occurrence,child) ∉ before.edges := by
          apply Classical.byContradiction
          intro none
          apply novel
          refine ⟨entailed,?_⟩
          intro child member
          by_cases found : (packet.site.occurrence,child) ∈ before.edges
          · exact found
          · exact False.elim (none ⟨child,member,found⟩)
        obtain ⟨child,member,absent⟩ := missing
        exact ⟨.edge packet.site.occurrence child,absent,(installed_committed before packet emitted).2 child member⟩
      · exact ⟨.constraints packet,entailed,(installed_committed before packet emitted).1⟩
  | merge first last _ _ _ novel =>
      exact ⟨.alias first.occurrence.identity last.occurrence.identity,novel,merged_inputs before first last⟩
  | refresh focus context certificate source member unknown known => exact ⟨.known source,unknown,known⟩

noncomputable def remaining (facts : List (Fact roles)) (state : State roles) : Nat := by
  classical
  exact facts.foldr (fun fact count => if Holds state fact then count else count+1) 0

private theorem remaining_cons (fact : Fact roles) (rest : List (Fact roles)) (state : State roles) :
    remaining (fact :: rest) state = if Holds state fact then remaining rest state else remaining rest state+1 := by
  classical
  rfl

theorem remaining_monotone (facts : List (Fact roles)) (growth : Extends before after) :
    remaining facts after ≤ remaining facts before := by
  classical
  induction facts with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
      rw [remaining_cons,remaining_cons]
      by_cases old : Holds before fact
      · have current := monotone growth fact old
        simp only [ite_eq_left old,ite_eq_left current]; exact ih
      · by_cases current : Holds after fact <;> simp [current,old] <;> omega

theorem remaining_decreases (facts : List (Fact roles)) (growth : Extends before after)
    (fact : Fact roles) (member : fact ∈ facts) (old : ¬ Holds before fact) (current : Holds after fact) :
    remaining facts after < remaining facts before := by
  classical
  induction facts with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have tail := remaining_monotone rest growth
        rw [remaining_cons,remaining_cons]
        simp only [ite_eq_right old,ite_eq_left current]
        omega
      · have tail := ih member
        rw [remaining_cons,remaining_cons]
        by_cases was : Holds before head
        · have now := monotone growth head was
          simp only [ite_eq_left was,ite_eq_left now]; exact tail
        · by_cases now : Holds after head <;> simp [now,was] <;> omega

/-- A precise finite-support premise over reachable updates. No constructor
from Checked alone is supplied or claimed by this module. -/
structure FiniteBasis (registry : Registry) (root : Occurrence roles) (initial : State roles) where
  facts : List (Fact roles)
  covers : ∀ before after, B4Target.Steps (Step registry root) initial before → Step registry root before after →
    ∃ fact ∈ facts, ¬ Holds before fact ∧ Holds after fact

theorem accessible_of_finite_basis (basis : FiniteBasis registry root start) :
    Acc (fun next current => Step registry root current next) start := by
  have accessible : ∀ state, B4Target.Steps (Step registry root) start state →
      Acc (fun next current => Step registry root current next) state := by
    intro state
    induction state using (measure (remaining basis.facts)).wf.induction with
    | h state ih =>
      intro path
      refine Acc.intro state ?_
      intro next update
      obtain ⟨fact,member,old,current⟩ := basis.covers state next path update
      exact ih next (remaining_decreases basis.facts (step_extends update) fact member old current) (.tail path update)
  exact accessible start .refl

theorem finite_interval_paterson (checked : DeclarationChecked constructors roles declaration)
    (clause : Clause) (member : clause ∈ declaration.requirements)
    (lower upper : Nat → Pattern) :
    Roles.argsSize (counted (substArgs lower clause.arguments)) +
        Roles.argsSize (counted (substArgs upper clause.arguments)) <
      Roles.argsSize (counted (substArgs lower declaration.head)) +
        Roles.argsSize (counted (substArgs upper declaration.head)) :=
  Nat.add_lt_add (checked.captureStable clause member lower).1 (checked.captureStable clause member upper).1

end

end Yulang.GeneralNominalSaturationProgress
