import Yulang.GeneralDictionaryDefault214ActualBodyFrame

/-! Normalized explicit and positional-default supports produce registered
head-origin witnesses. Snapshot and current merged requests retain their own
trace-derived target separation; neither support is silently discarded. -/
namespace Yulang.GeneralDictionaryDefault214ActualEffects
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefault214ActualReadback (Actual registered_input_actual)
open GeneralDictionaryDefault214ActualSupport (registered_packets registered_input center_list_actual)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem body_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (supplied : Supplies roles plan.packet.declaration outputName body)
    (separate : fresh context.state.seed invocation declaration 8 owner position ≠ target)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈ bodySources plan target body) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  cases supplied with
  | explicit equation present named =>
      rcases List.mem_cons.mp member with equal | member
      · exact False.elim (separate equal)
      · obtain ⟨name,used,equal⟩ := List.mem_map.mp member
        rcases plan.packet.checked.scope.2.1 equation present name used with input | output
        · rw [← equal]
          exact registered_input_actual path plan registered name input
        · have excluded := (GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
            (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
            source bound path plan.packet (registered_packets path plan registered) (by decide : 7 ≤ 8) name).1
          apply False.elim
          apply excluded
          simpa only [Plan.binder,output,ite_true] using equal.symm
  | default term absent declared =>
      change _ ∈ GeneralDictionaryDefaultModeEffects213.bodySources plan target _ at member
      unfold GeneralDictionaryDefaultModeEffects213.bodySources GeneralDictionaryDefaultModeSupport213.schemaSources bodySchema at member
      cases compiled : compileBody plan (.default plan.packet.declaration.role outputName term) with
      | none => simp [compiled] at member
      | some expression =>
          simp only [compiled,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_cons] at member
          rcases member with equal | read
          · exact False.elim (separate equal)
          · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at read
            obtain ⟨name,_,equal⟩ := List.mem_map.mp read
            apply center_list_actual source path plan.input (registered_input path plan registered)
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

theorem class_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (separate : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests view focus,
      fresh context.state.seed invocation declaration 8 owner position ≠ output.target)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈ classSources view focus plan) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp within with equal | within
  · exact False.elim (separate output requested equal)
  · obtain ⟨body,found,within⟩ := List.mem_flatMap.mp within
    have supplied := (lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 output.name body).mp
      (Option.mem_toList.mp found)
    exact body_support_actual source bound path plan registered supplied (separate output requested) within

theorem request_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus) (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ≠ output.target := by
  obtain ⟨site,registered,_,present⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  intro equal
  exact GeneralNominalCenteredAllocation.outside_pool source high
    (equal.symm ▸ (GeneralDictionaryDefaultEnumeration208.source_pool source bound path).2 site registered output present)

theorem effect_plan_registered
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ effect ∈ state.effects, effect.plan ∈ state.core.plans := by
  induction path with
  | refl => intro effect member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
        intro prior member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih prior member)

theorem effect_snapshot
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ effect ∈ state.effects, ∃ before,
      B4Target.Steps (Step registry root) (initial context root) before ∧ effect.snapshot = before.core := by
  induction path with
  | refl => intro effect member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
        intro prior member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨before,path,enabled.snapshot_eq⟩
        · exact ih prior member

theorem live_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (registered : effect ∈ state.effects)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈
      classSources state.core effect.plan.packet.site.occurrence effect.plan) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin :=
  class_support_actual source bound path effect.plan (effect_plan_registered path effect registered)
    (fun _ requested => request_separate source bound path requested (by decide)) member

theorem snapshot_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (registered : effect ∈ state.effects)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈
      classSources effect.snapshot effect.plan.packet.site.occurrence effect.plan) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  obtain ⟨before,prior,snapshot⟩ := effect_snapshot path effect registered
  apply class_support_actual source bound path effect.plan (effect_plan_registered path effect registered) _ member
  intro output requested
  rw [snapshot] at requested
  exact request_separate source bound prior requested (by decide)

end Yulang.GeneralDictionaryDefault214ActualEffects
