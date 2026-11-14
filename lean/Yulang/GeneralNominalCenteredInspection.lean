import Yulang.GeneralNominalCenteredBoundary
import Yulang.GeneralNominalPacketCodes

/-! Explicit input names cover every recursive inspection position. Selection
therefore supplies the centered cycle and decision guards; ordinary preparation,
value support, and a common branch model remain separate obligations. -/
namespace Yulang.GeneralNominalCenteredInspection
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDeclarations GeneralSourceDictionaries

def Complete (report : Report state) : Prop := report.inspected.length = report.tests.length

private theorem append_complete (one : Complete (first : Report state))
    (two : Complete (last : Report state)) : Complete (first.append last) := by
  simp only [Complete,Report.append,List.length_append] at *
  omega

private theorem visit_complete (one : Complete (report : Report state)) :
    Complete (report.visit bounds (some origin) test) := by
  simp only [Complete,Report.visit,Option.toList,List.map_cons,List.map_nil,
    List.length_append,List.length_cons,List.length_nil] at *
  omega

mutual
  theorem inspect_complete (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Origin) : Complete (inspect state query bounds (some origin)) := by
    cases query with
    | variables | deferred => simp [inspect,Complete,block]
    | scalar base =>
      simp only [inspect]
      apply visit_complete
      split
      · simp [Complete]
      · split
        · split <;> simp [Complete]
        · simp [Complete]
        · simp [Complete,block]
    | node shape children =>
      simp only [inspect]
      apply visit_complete
      split
      · split
        · exact many_complete state children _ _ 0 (fun _ _ => ⟨_,rfl⟩)
        · simp [Complete,block]
      · simp [Complete]
      · simp [Complete,block]
    | nominal name children =>
      simp only [inspect]
      apply visit_complete
      split
      · split <;> simp [Complete,block]
      · split
        · split
          · simp [Complete,block]
          · split
            · exact many_complete state children _ _ 0 (fun _ _ => ⟨_,rfl⟩)
            · split
              · simp [Complete,block]
              · split
                · split
                  · simp [Complete,block]
                  · exact append_complete
                      (many_complete state children _ _ 0 (fun _ _ => ⟨_,rfl⟩))
                      (many_complete state children _ _ 0 (fun _ _ => ⟨_,rfl⟩))
                · simp [Complete]
        · simp [Complete]
    termination_by sizeOf query

  theorem many_complete (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (known : ∀ index, index < bounds.length → ∃ origin, origins (offset+index) = some origin) :
      Complete (inspectMany state queries bounds origins offset) := by
    cases queries with
    | nil => cases bounds <;> simp [inspectMany,Complete]
    | cons query rest =>
      cases bounds with
      | nil => simp [inspectMany,Complete]
      | cons head tail =>
        simp only [inspectMany]
        apply append_complete
        · obtain ⟨origin,same⟩ := known 0 (by simp)
          simp only [Nat.add_zero] at same
          rw [same]
          exact inspect_complete state query head origin
        · apply many_complete state rest tail origins (offset+1)
          intro index inside
          simpa only [Nat.add_assoc,Nat.add_comm 1 index] using known (index+1) (by simpa using Nat.succ_lt_succ inside)
    termination_by sizeOf queries
end

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

theorem plan_complete (plan : Plan roles)
    (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.input.occurrence = some plan.packet.bounds) :
    Complete (inspection plan) := by
  have length : plan.packet.bounds.length = (roles plan.input.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length plan.packet.context.state.base
      (List.ofFn plan.input.occurrence.demand.arguments) plan.packet.bounds located
  apply many_complete
  intro index inside
  have bounded : index < (roles plan.input.occurrence.demand.role).arity := by simpa only [length] using inside
  refine ⟨.source (plan.input.center ⟨index,bounded⟩),?_⟩
  simp [Site.observed,bounded]

theorem selected_guards
    (selected : GeneralNominalCenteredBoundary.Local registry state root (.selected key children)) :
    DecisionGuard registry state root ∧ ¬ RootCycle state root ∧ ¬ CandidateCycle registry state root := by
  cases selected with
  | selected safe unique =>
    exact ⟨Classical.byContradiction (fun missing => safe.2.2.2 (Or.inr missing)),
      fun cycle => safe.2.1 (Or.inr cycle),fun cycle => safe.2.2.1 (Or.inr cycle)⟩

theorem selected_safe
    (selected : GeneralNominalCenteredBoundary.Local registry state root (.selected key children))
    (plan : Plan roles) (recorded : plan.input ∈ state.sites) (input : plan.input.occurrence = root)
    (registryEq : plan.packet.registry = registry) (contextEq : plan.packet.context = state.erased.current.context)
    (visible : plan.packet.declaration ∈ registry.declarations)
    (role : plan.packet.declaration.role = root.demand.role)
    (ready : GeneralNominalRecursiveCandidates.HeadReady registry plan.packet.context root plan.packet.declaration)
    (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context root = some plan.packet.bounds) :
    Safe state plan := by
  refine ⟨plan_complete plan (input ▸ located),?_⟩
  intro entry member cycle
  exact (selected_guards selected).2.2
    ⟨plan,recorded,input,registryEq,contextEq,visible,role,ready,located,entry,member,cycle⟩

theorem selected_alternatives
    (selected : GeneralNominalCenteredBoundary.Local registry state root (.selected key children))
    (input : Site roles) (recorded : input ∈ state.sites) (same : input.occurrence = root) :
    AlternativesSafe registry state input := by
  intro plan inputEq registryEq contextEq visible role ready located
  apply selected_safe selected plan (inputEq ▸ recorded) (inputEq ▸ same) registryEq contextEq visible
  · simpa only [same] using role
  · simpa only [same,contextEq] using ready
  · simpa only [same] using located

theorem selected_guard_reduction (plan : Plan roles)
    (selected : GeneralNominalCenteredBoundary.Local registry state plan.packet.site.occurrence (.selected key children))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (recorded : plan.input ∈ state.sites) (support : List (Occurrence roles)) :
    PacketGuard state plan support ↔
      GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
        ∃ model, Models state model ∧ plan.Holds model := by
  constructor
  · intro guard
    exact ⟨guard.2.1,guard.2.2.2.2.2.2⟩
  · rintro ⟨values,model⟩
    obtain ⟨reg,ctx,_,visible,role,located,prepared,_⟩ := enabled.1
    have ready : GeneralNominalRecursiveCandidates.HeadReady registry plan.packet.context
        plan.packet.site.occurrence plan.packet.declaration := by
      rw [← reg]
      obtain ⟨metadata,linked,fresh,bounds,found,finished,_,m,branch⟩ := prepared
      exact ⟨metadata,linked,fresh,bounds,found,finished,m,branch.1,branch.2.1⟩
    have localGuards := selected_guards selected
    refine ⟨recorded,values,?_,selected_safe selected plan recorded plan.input_exact reg ctx visible role ready located,?_,?_,model⟩
    · simpa only [DecisionGuard,reg,ctx] using localGuards.1
    · simpa only [reg] using selected_alternatives selected plan.input recorded plan.input_exact
    · simpa only [reg] using localGuards.2

theorem selected_installable_iff (plan : Plan roles)
    (selected : GeneralNominalCenteredBoundary.Local registry state plan.packet.site.occurrence (.selected key children))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (recorded : plan.input ∈ state.sites) :
    GeneralNominalCenteredBoundary.Installable registry state plan ↔
      ∃ support, GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
        ∃ model, Models state model ∧ plan.Holds model := by
  constructor
  · rintro ⟨_,support,guard⟩
    exact ⟨support,(selected_guard_reduction plan selected enabled recorded support).mp guard⟩
  · rintro ⟨support,remaining⟩
    exact ⟨enabled,support,(selected_guard_reduction plan selected enabled recorded support).mpr remaining⟩

theorem unmerged_blocks {roles : Roles.RoleDecls} {registry : Registry}
    {state : State roles} {plan : Plan roles} {other : GeneralNominalDemandMerging.Site roles}
    (recorded : other ∈ state.erased.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs state.erased.current plan.packet.site other)
    (apart : ¬ GeneralNominalSaturationState.Alias state.erased.current
      plan.packet.site.occurrence.identity other.occurrence.identity) :
    ¬ GeneralNominalCenteredBoundary.Installable registry state plan :=
  fun enabled => apart (enabled.1.2.2 other recorded same)

end Yulang.GeneralNominalCenteredInspection
