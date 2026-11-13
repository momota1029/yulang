import Yulang.GeneralNominalCenteredEnumeration

/-! The center namespaces are disjoint from ordinary allocation. Registered
plans retain their nested actual-use equations throughout the centered trace. -/
namespace Yulang.GeneralNominalCenteredAllocation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredTrace GeneralNominalCenteredAncestry GeneralNominalCenteredEnumeration
open GeneralNominalAllocation (keys declarationKeys origin)
open GeneralNominalInvocationAncestry (allocationPool)
open GeneralNominalActualTraceSupport (pool)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem declaration_key_purpose (member : key ∈ declarationKeys invocation declaration) : key.2.2.1 ≤ 6 := by
  simp only [declarationKeys,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (⟨name,_,rfl | rfl⟩ | ⟨name,_,rfl⟩) | ⟨clause,_,(rfl | ⟨index,_,rfl | rfl⟩) | ⟨equation,_,rfl⟩⟩
  all_goals simp only [origin]; omega

theorem key_purpose (member : key ∈ keys registry invocation) : key.2.2.1 ≤ 6 := by
  obtain ⟨declaration,_,member⟩ := List.mem_flatMap.mp member
  exact declaration_key_purpose member

theorem fresh_identity (seed : Nat) (first last : GeneralNominalIdentities.Origin) :
    fresh seed first.1 first.2.1 first.2.2.1 first.2.2.2.1 first.2.2.2.2 =
      fresh seed last.1 last.2.1 last.2.2.1 last.2.2.2.1 last.2.2.2.2 ↔ first = last :=
  GeneralNominalIdentities.source_identity seed first last

theorem fresh_namespaces (different : purpose ≠ other) :
    fresh seed invocation declaration purpose owner position ≠
      fresh seed next nextDeclaration other nextOwner nextPosition := by
  intro same
  have keys := (GeneralNominalIdentities.source_identity seed _ _).mp same
  exact different (congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) keys)

theorem outside_pool (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (centerPurpose : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉ pool registry context root limit := by
  intro member
  rcases List.mem_append.mp member with original | allocated
  · have below := source.below_seed _ original
    have above := GeneralNominalIdentities.source_above_seed context.state.seed (invocation,declaration,purpose,owner,position)
    change context.state.seed < fresh context.state.seed invocation declaration purpose owner position at above
    omega
  · obtain ⟨parent,_,member⟩ := List.mem_flatMap.mp allocated
    obtain ⟨key,present,equal⟩ := List.mem_map.mp member
    have same := (GeneralNominalIdentities.source_identity context.state.seed _ _).mp equal
    have bounded := key_purpose present
    have purposeEq := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) same
    change key.2.2.1 = purpose at purposeEq
    omega

theorem fresh_outside_raw_sources
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (centerPurpose : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.erased.current.context.state :=
  fun member => outside_pool source centerPurpose ((source_pool source bound path).1 member)

theorem compound_center_identity (plan : Plan roles)
    (one : ∀ name, GeneralDeclarationPatterns.normalize first ≠ .var name)
    (two : ∀ name, GeneralDeclarationPatterns.normalize last ≠ .var name) :
    plan.emittedCenter clause position first = plan.emittedCenter other index last ↔ clause = other ∧ position = index := by
  have firstEq : plan.emittedCenter clause position first = fresh plan.packet.context.state.seed
      plan.packet.site.occurrence.identity plan.packet.declaration.id 9 clause position := by
    unfold Plan.emittedCenter
    cases same : GeneralDeclarationPatterns.normalize first <;> first | exact False.elim (one _ same) | rfl
  have lastEq : plan.emittedCenter other index last = fresh plan.packet.context.state.seed
      plan.packet.site.occurrence.identity plan.packet.declaration.id 9 other index := by
    unfold Plan.emittedCenter
    cases same : GeneralDeclarationPatterns.normalize last <;> first | exact False.elim (two _ same) | rfl
  rw [firstEq,lastEq]
  constructor
  · intro equal
    have same := (GeneralNominalIdentities.source_identity plan.packet.context.state.seed _ _).mp equal
    exact ⟨congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) same,
      congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.2) same⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem registered_packets
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, plan.packet ∈ state.erased.current.packets := by
  induction path with
  | refl => intro plan impossible; cases impossible
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro other member
      rcases List.mem_cons.mp member with rfl | old
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih other old)

theorem registered_plan_holds
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (registered : plan ∈ state.plans) (valid : Models state model) : plan.Holds model :=
  ⟨valid.1.2.1 plan.packet (registered_packets path plan registered),valid.2.2 plan registered⟩

theorem registered_nested_name
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (registered : plan ∈ state.plans) (valid : Models state model)
    (use : GeneralNominalMaterialization.Use) (present : use ∈ plan.headSchema.variables)
    (actual : use.mode = .actual) :
    GeneralNominalOriginTerms.Same model use.origin (.source (plan.binder use.name)) :=
  capture_agreement plan use.name model (registered_plan_holds path registered valid) use present rfl actual

theorem registered_nested_argument
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (registered : plan ∈ state.plans) (valid : Models state model)
    (use : GeneralNominalMaterialization.Use) (present : use ∈ plan.headSchema.variables)
    (actual : use.mode = .actual)
    (needed : use.name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet use.name) :
    NominalArgument.Holds
      ⟨⟨(GeneralNominalPacketSupport.capture plan.packet).inputs use.name,plan.binder use.name⟩,use.origin⟩ model :=
  ⟨(registered_plan_holds path registered valid).2.2.1 use.name needed,
    registered_nested_name path registered valid use present actual⟩

theorem registered_child_names
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (registered : plan ∈ state.plans) (valid : Models state model)
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
    (plan.childSite clause signature).Holds model ∧
      plan.SchemaHolds (plan.schema (plan.childRequests clause signature)) model :=
  (registered_plan_holds path registered valid).2.2.2.2.2.2 clause present signature

end Yulang.GeneralNominalCenteredAllocation
