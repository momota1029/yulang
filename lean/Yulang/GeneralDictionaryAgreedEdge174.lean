import Yulang.GeneralNominalActualAgreedBoundary
import Yulang.GeneralNominalPatersonLineage

/-! A genuine restricted producer of child accessibility: role-stratified
registries. The restriction is a declaration-graph condition and is NOT a
language rejection rule or a proof for general Paterson-recursive registries.
No source model, finite label readback, or selected-packet installation guard
is assumed. Both provenance policies have the same child-role descent. -/
namespace Yulang.GeneralDictionaryAgreedEdge174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal
open CommonRoleOutermostResolver (Child)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}
variable {defer : Bool} {gap : GapPredicate roles}

/-- A rank on the declared role-dependency graph, not on runtime states. -/
def RoleStratified (registry : Registry) (rank : Nat → Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, ∀ clause ∈ declaration.requirements,
    rank clause.role < rank declaration.role

/-- The selected child really has a role mentioned by this declaration's
where-clause. This is a syntactic selection witness, not installation. -/
theorem selected_child_role
    (selected : Local defer gap registry state parent (.selected key children))
    (member : child ∈ children) :
    ∃ declaration ∈ registry.declarations, ∃ clause ∈ declaration.requirements,
      declaration.role = parent.demand.role ∧ clause.role = child.demand.role := by
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context parent key children := by
    cases selected with
    | selected _ unique => exact unique.1
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  let packet : Packet roles := ⟨registry,state.current.context,
    GeneralNominalDemandMerging.pointSite parent,declaration,checked,bounds⟩
  have present : child ∈ packet.children := by
    change child ∈ GeneralNominalAllocation.children state.current.context.state registry parent declaration checked
      (GeneralNominalRecursiveInspection.bindings state.current.context.state
        (GeneralNominalRecursiveCandidates.report state.current.context declaration bounds))
    rw [← emitted]
    exact member
  obtain ⟨clause,present,signature,same⟩ :=
    GeneralNominalPatersonLineage.emitted_clause packet child present
  refine ⟨declaration,visible,clause,present,role,?_⟩
  rw [same]
  rfl

theorem child_role_decreases (stratified : RoleStratified registry rank)
    (edge : Child (Local defer gap registry state) child parent) :
    rank child.demand.role < rank parent.demand.role := by
  obtain ⟨key,children,selected,member⟩ := edge
  obtain ⟨declaration,visible,clause,present,parentRole,childRole⟩ := selected_child_role selected member
  rw [← parentRole,← childRole]
  exact stratified declaration visible clause present

/-- Unconditional within the explicit role-stratified registry fragment;
where-recursive same-role implementations are outside this fragment. -/
theorem whereAccessible (stratified : RoleStratified registry rank) (root : Occurrence roles) :
    Acc (Child (Local defer gap registry state)) root := by
  induction root using (measure (fun root : Occurrence roles => rank root.demand.role)).wf.induction with
  | h root ih =>
    constructor
    intro child edge
    exact ih child (child_role_decreases stratified edge)

theorem boundary_whereAccessible (stratified : RoleStratified registry rank) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local
      (GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state)) root := by
  have acc := whereAccessible (defer := defer) (gap := gap) (state := state) stratified root
  induction acc with
  | intro parent below ih =>
    constructor
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,
      (GeneralNominalActualAgreedBoundary.local_correspondence defer gap registry state parent _).mp selected,member⟩

/-- Leaf registries allow the constant-zero role rank. -/
theorem leaves_stratified
    (leaves : ∀ declaration ∈ registry.declarations, declaration.requirements = []) :
    RoleStratified registry (fun _ => 0) := by
  intro declaration visible clause member
  rw [leaves declaration visible] at member
  cases member

theorem leaf_whereAccessible
    (leaves : ∀ declaration ∈ registry.declarations, declaration.requirements = [])
    (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local
      (GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state)) root :=
  boundary_whereAccessible (leaves_stratified leaves) root

/-- Reordering declarations/where clauses preserves this fragment with the
same role rank. This is not canonicalLocalOrder for two different final states. -/
theorem stratified_reorders (order : GeneralRegistryReordering.Reorders registry other)
    (stratified : RoleStratified registry rank) : RoleStratified other rank := by
  intro declaration visible clause member
  obtain ⟨old,present,changed⟩ := GeneralRegistryReordering.reorders_visible_back order declaration visible
  rw [← changed.role]
  exact stratified old present clause (changed.requirements.mem_iff.mpr member)

/-- A concrete selected descent path, counted by its edges. -/
inductive Descent (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Nat → Occurrence roles → Prop
  | root : Descent defer gap registry state root 0 root
  | next : Descent defer gap registry state root depth parent →
      Child (Local defer gap registry state) child parent →
      Descent defer gap registry state root (depth + 1) child

theorem descent_bounded (stratified : RoleStratified registry rank)
    (path : Descent defer gap registry state root depth child) :
    depth + rank child.demand.role ≤ rank root.demand.role := by
  induction path with
  | root => exact Nat.zero_add _ ▸ Nat.le_refl _
  | next path edge ih =>
    have decrease := child_role_decreases stratified edge
    omega

end Yulang.GeneralDictionaryAgreedEdge174
