import Yulang.GeneralDeclarativeStoppedDiagnostic341
import Yulang.GeneralStoppedPlacement335
import Yulang.GeneralStoppedOrdinarySite335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedPaired341
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Models)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralStoppedPlacement335 (SameDemand demands_models)
open CommonRoleOutermostResolver (All₂ Frontier Resolves Summarizes Classify Tree Dictionary Result)
open GeneralNominalVersionedDiagnostic232 (vocabulary)

noncomputable def activeDemand (s : State roles) (site : Site roles) : Demand :=
  { demand site with outputs := GeneralNominalCenteredHeadOutputs.requests s.core site.occurrence }

/-- Actual registered site and all of its current class requests.
Endpoint/center slots may be represented by different logical names
only with the relevant checked aliases; output order and targets are
literal, not just model-equivalent. -/
def Placement {roles : Roles.RoleDecls} (s : State roles)
    (view : GeneralDeclarativeHead320.State) (focus : Occurrence roles) (logical : Demand) : Prop :=
  ∃ site ∈ s.core.sites, site.occurrence = focus ∧ SameDemand view (activeDemand s site) logical

theorem placement_targets {roles : Roles.RoleDecls} {s : State roles}
    {focus : Occurrence roles} {logical : Demand} {view : GeneralDeclarativeHead320.State}
    (place : Placement s view focus logical) :
    logical.outputs = GeneralNominalCenteredHeadOutputs.requests s.core focus := by
  obtain ⟨_,_,raw,matched⟩ := place
  rw [← raw]
  exact matched.outputs.symm

structure Bridge {roles : Roles.RoleDecls} (b : B4TargetV8.SourceBoundary (vocabulary roles))
    (r : Registry) (s : State roles) (root : Occurrence roles)
    (view : GeneralDeclarativeHead320.State) (rel : Occurrence roles → Demand → Prop)
    (rule : Demand → Frontier Demand → Prop) : Prop where
  placed : ∀ raw logical, rel raw logical → Placement s view raw logical
  children : ∀ raw, Generated s.core.erased.current root raw → ∀ key kids,
    B4TargetV8.Local b r s raw (.selected key kids) →
    ∀ d ∈ kids, Generated s.core.erased.current root d
  positive : ∀ raw logical, rel raw logical → Generated s.core.erased.current root raw →
    ∀ key kids, B4TargetV8.Local b r s raw (.selected key kids) →
    ∃ emitted, rule logical (.selected key emitted) ∧ All₂ rel kids emitted

section
variable {roles : Roles.RoleDecls} {b : B4TargetV8.SourceBoundary (vocabulary roles)}
  {r : Registry} {s : State roles} {root : Occurrence roles} {view : GeneralDeclarativeHead320.State}
  {rel : Occurrence roles → Demand → Prop} {rule : Demand → Frontier Demand → Prop}

mutual
/-- A relational, position-sensitive form of exact positive projection.
The same raw occurrence need not have a unique literal endpoint
representation in every caller. Indeed the compiler may remint
fresh logical names; the paired children are still checked in order. -/
theorem tree (h : Bridge b r s root view rel rule)
    (raw : Occurrence roles) (logical : Demand) (opened : rel raw logical)
    (live : Generated s.core.erased.current root raw) (t : Tree) (dict : Dictionary)
    (resolved : Resolves (B4TargetV8.Local b r s) raw t)
    (success : Summarizes t (.selected dict)) : Resolves rule logical t := by
  cases resolved with
  | pending _ => cases success
  | rejected _ => cases success
  | ambiguous _ => cases success
  | selected got tails =>
    obtain ⟨_,current,pairs⟩ := h.positive raw logical opened live _ _ got
    cases success with
    | selected result combine =>
      cases combine with
      | selected _ =>
        subst_vars
        exact .selected current (forest h _ _ pairs (h.children raw live _ _ got) _ _ tails result)
termination_by sizeOf t

theorem forest (h : Bridge b r s root view rel rule)
    (raw : List (Occurrence roles)) (logical : List Demand) (pairs : All₂ rel raw logical)
    (live : ∀ child ∈ raw, Generated s.core.erased.current root child) (ts : List Tree) (ds : List Dictionary)
    (resolved : All₂ (Resolves (B4TargetV8.Local b r s)) raw ts)
    (success : All₂ Summarizes ts (ds.map Result.selected)) : All₂ (Resolves rule) logical ts := by
  cases ds with
  | nil => cases success; cases resolved; cases pairs; exact .nil
  | cons hd rest =>
    cases success with
    | cons here later =>
      cases resolved with
      | cons selected remaining =>
        cases pairs with
        | cons one more =>
          exact .cons (tree h _ _ one (live _ List.mem_cons_self) _ hd selected here)
            (forest h _ _ more (fun _ made => live _ (List.mem_cons_of_mem _ made)) _ rest remaining later)
termination_by sizeOf ts
end

theorem exact (h : Bridge b r s root view rel rule) (matchRoot : rel root logical)
    (raw : Resolves (B4TargetV8.Local b r s) root diagnostic)
    (success : Summarizes diagnostic (.selected dict)) :
    logical.outputs = GeneralNominalCenteredHeadOutputs.requests s.core root ∧
    Resolves rule logical diagnostic ∧ Classify rule logical (.selected dict) := by
  have checked := tree h root logical matchRoot .root diagnostic dict raw success
  exact ⟨placement_targets (h.placed root logical matchRoot),checked,⟨diagnostic,checked,success⟩⟩

end
end Yulang.GeneralDeclarativeStoppedPaired341
