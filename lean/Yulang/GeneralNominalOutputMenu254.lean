import Yulang.GeneralNominalProducerOrder254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalOutputMenu254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralNominalCapturedOutput254 (bodyDepth)
variable {roles : Roles.RoleDecls} {state : State roles}

def names (registry : Registry) (root : Occurrence roles) : List Nat :=
 root.demand.outputs.map GeneralSourceState.Output.name ++
 registry.declarations.flatMap fun declaration =>
 declaration.requirements.flatMap fun clause => clause.outputs.map Equation.name

theorem clause_name (visible : declaration ∈ registry.declarations)
 (member : clause ∈ declaration.requirements) (found : equation ∈ clause.outputs) :
 equation.name ∈ names registry root :=
 List.mem_append_right _ (List.mem_flatMap.mpr ⟨declaration,visible,
   List.mem_flatMap.mpr ⟨clause,member,List.mem_map.mpr ⟨equation,found,rfl⟩⟩⟩)

theorem child_name (packet : GeneralNominalSaturationState.Packet roles)
 (visible : packet.declaration ∈ registry.declarations)
 (member : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
 (request : GeneralSourceState.Output)
 (requested : request ∈ (GeneralNominalVersionedFrame231.clauseChild packet clause signature).demand.outputs) :
 request.name ∈ names registry root := by
 obtain ⟨equation,present,same⟩ := List.mem_map.mp requested
 have equal := congrArg GeneralSourceState.Output.name same
 exact equal ▸ clause_name visible member present

/-- One source/registry list bounds output request names at every recorded
center site, independently of refresh count and output target allocation. -/
theorem source_names
 (path : B4Target.Steps (Step registry root) (initial context root) state) :
 ∀ site ∈ state.core.sites, ∀ output ∈ site.occurrence.demand.outputs, output.name ∈ names registry root := by
 induction path with
 | refl =>
   intro site member output requested
   cases List.mem_singleton.mp member
   exact List.mem_append_left _ (List.mem_map.mpr ⟨output,requested,rfl⟩)
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
     intro site member output requested
     change site ∈ before.core.sites ++ GeneralNominalVersionedChildren232.emitted effect.plan at member
     rcases List.mem_append.mp member with old | added
     · exact ih site old output requested
     · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
       have present := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
       exact child_name effect.plan.packet (GeneralNominalVersionedMixedAncestry237.frame enabled).visible present _ output requested

/-- Explicit implementation RHSs and positional defaults retain provenance.
Only finite source-request names are queried from the possibly infinite role map. -/
def bodies (registry : Registry) (roles : Roles.RoleDecls) (outputNames : List Nat) : List Body :=
 registry.declarations.flatMap fun declaration =>
   declaration.associated.map Body.explicit ++
   outputNames.flatMap fun name =>
     (((roles declaration.role).assoc name).join.toList.map fun rhs => Body.default declaration.role name rhs)

theorem supplied_mem (visible : declaration ∈ registry.declarations)
 (named : name ∈ outputNames) (supplied : Supplies roles declaration name body) :
 body ∈ bodies registry roles outputNames := by
 apply List.mem_flatMap.mpr
 refine ⟨declaration,visible,?_⟩
 cases supplied with
 | explicit equation member _ => exact List.mem_append_left _ (List.mem_map.mpr ⟨equation,member,rfl⟩)
 | default rhs _ declared =>
   apply List.mem_append_right
   apply List.mem_flatMap.mpr
   refine ⟨name,named,?_⟩
   simp only [declared,Option.join_some,Option.toList_some,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]

def budget (registry : Registry) (roles : Roles.RoleDecls) (root : Occurrence roles) : Nat :=
 GeneralNominalProducerOrder254.ceiling ((bodies registry roles (names registry root)).map bodyDepth)

theorem body_bound
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body) :
 bodyDepth body ≤ budget registry roles root := by
 have named := source_names path plan.input frame.center_recorded output
   (by simpa only [plan.input_exact,frame.occurrence_eq] using requested)
 exact GeneralNominalProducerOrder254.below_ceiling
   (List.mem_map.mpr ⟨body,supplied_mem frame.visible named supplied,rfl⟩)
end Yulang.GeneralNominalOutputMenu254
