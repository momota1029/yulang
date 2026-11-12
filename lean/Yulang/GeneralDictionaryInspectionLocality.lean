import Yulang.GeneralDictionaryInspectionTransport

/-! Computable descriptor-read footprints for recursive inspection. The global
normalized-head/shape view is fixed, but nominal descriptors may change outside
the finite query footprint. Variable queries have empty footprint: their bound
values and descendants are not inspected. The footprint is conservative on
mismatches and nonpoint endpoints; it is not claimed minimal. -/
namespace Yulang.GeneralDictionaryInspectionLocality
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context)
open GeneralDictionaryInspectionTransport

mutual
  def footprint (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state) :
      List (Fin state.base.slots) :=
    match query with
    | .variables _ | .deferred _ => []
    | .scalar _ => [bounds.1]
    | .node _ patterns =>
        match state.view.heads bounds.1,state.view.heads bounds.2 with
        | .structural _ children,.structural _ targets =>
            footprints state patterns ((List.ofFn children).zip (List.ofFn targets))
        | _,_ => []
    | .nominal _ patterns =>
        [bounds.1,bounds.2] ++
          (match state.nominals bounds.1 with
           | some descriptor => match typeArguments descriptor.arguments with
             | some arguments => footprints state patterns arguments
             | none => []
           | none => []) ++
          (match state.nominals bounds.2 with
           | some descriptor => match typeArguments descriptor.arguments with
             | some arguments => footprints state patterns arguments
             | none => []
           | none => [])
  termination_by sizeOf query
  def footprints (state : GeneralNominalState.State) : List Query → List (Bounds state) →
      List (Fin state.base.slots)
    | query :: queries,bound :: bounds => footprint state query bound ++ footprints state queries bounds
    | _,_ => []
  termination_by queries _ => sizeOf queries
end

@[simp] theorem variables_footprint (state : GeneralNominalState.State) (names : List Nat)
    (bounds : Bounds state) : footprint state (.variables names) bounds = [] := by simp [footprint]

@[simp] theorem transfer_append (context : Context) (next : Observation context.state)
    (first last : Report context.state) :
    transferReport context next (first.append last) =
      (transferReport context next first).append (transferReport context next last) := by
  simp [transferReport,Report.append,List.map_append]

@[simp] theorem transfer_visit (context : Context) (next : Observation context.state)
    (bounds : Bounds context.state) (origin : Option Origin) (test : Test) (value : Report context.state) :
    transferReport context next (Report.visit bounds origin test value) =
      @Report.visit (reobserve context next).state bounds origin test (transferReport context next value) := rfl

mutual
  theorem inspect_local (context : Context) (next : Observation context.state)
      (view : next.view = context.state.view)
      (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
      (same : ∀ slot ∈ footprint context.state query bounds,
        next.nominals slot = context.state.nominals slot) :
      inspect (reobserve context next).state query bounds origin =
        transferReport context next (inspect context.state query bounds origin) := by
    rcases next with ⟨v,n,c,o⟩
    dsimp only at view
    subst v
    let next : Observation context.state := ⟨context.state.view,n,c,o⟩
    cases query with
    | variables names =>
      simp only [inspect,transferReport,capture,List.map_map,Function.comp_def]
    | deferred term => simp only [inspect,block,transferReport]; rfl
    | scalar expected =>
      have low := same bounds.1 (by simp [footprint])
      dsimp only at low
      simp only [inspect,reobserve,low]
      repeat' split
      all_goals rfl
    | node expected patterns =>
      simp only [footprint] at same
      simp only [inspect,reobserve]
      split
      · rename_i lower children upper targets observed
        split
        · rw [inspectMany_local context next rfl patterns _ _ _ (by simpa [targets,observed] using same)]
          rfl
        · rfl
      · rfl
      · rfl
    | nominal expected patterns =>
      have low := same bounds.1 (by simp [footprint])
      dsimp only at low
      have high := same bounds.2 (by simp [footprint])
      dsimp only at high
      simp only [inspect,reobserve,low,high]
      split
      · repeat' split
        all_goals rfl
      · rename_i lower recorded
        split
        · split
          · rfl
          · rename_i arguments arguments_eq
            have left : ∀ slot ∈ footprints context.state patterns arguments,
                next.nominals slot = context.state.nominals slot := by
              intro slot member
              apply same slot
              simp only [footprint,recorded,arguments_eq,List.mem_append,List.mem_cons,List.not_mem_nil]
              exact Or.inl (Or.inr member)
            rw [inspectMany_local context next rfl patterns arguments _ _ left]
            split
            · rfl
            · split
              · rfl
              · rename_i upper upper_recorded
                split
                · split
                  · rfl
                  · rename_i targets targets_eq
                    have right : ∀ slot ∈ footprints context.state patterns targets,
                        next.nominals slot = context.state.nominals slot := by
                      intro slot member
                      apply same slot
                      simp only [footprint,upper_recorded,targets_eq,List.mem_append]
                      exact Or.inr member
                    rw [inspectMany_local context next rfl patterns targets _ _ right]
                    simp only [transfer_visit,transfer_append]
                    rfl
                · rfl
        · rfl
  termination_by sizeOf query
  theorem inspectMany_local (context : Context) (next : Observation context.state)
      (view : next.view = context.state.view)
      (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
      (same : ∀ slot ∈ footprints context.state queries bounds,
        next.nominals slot = context.state.nominals slot) :
      inspectMany (reobserve context next).state queries bounds origins index =
        transferReport context next (inspectMany context.state queries bounds origins index) := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany,transferReport] <;> rfl
    | cons query queries =>
      cases bounds with
      | nil => simp only [inspectMany,transferReport]; rfl
      | cons bound bounds =>
        rw [inspectMany,inspectMany,
          inspect_local context next view query bound (origins index)
            (fun slot member => same slot (by simpa only [footprints] using List.mem_append_left (footprints context.state queries bounds) member)),
          inspectMany_local context next view queries bounds origins (index+1)
            (fun slot member => same slot (by simpa only [footprints] using List.mem_append_right (footprint context.state query bound) member)),transfer_append]
  termination_by sizeOf queries
end

/-- The finite descriptor condition implies equality of the actual candidate
report, including all captures, checked intervals, anchors and tests. -/
theorem report_local (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds context.state))
    (same : ∀ slot ∈ footprints context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
      next.nominals slot = context.state.nominals slot) :
    GeneralNominalRecursiveCandidates.report (reobserve context next) declaration bounds =
      transferReport context next (GeneralNominalRecursiveCandidates.report context declaration bounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  have queries : GeneralNominalInspection.queries (reobserve context next).state
      (reobserve context next).interpretation declaration =
      GeneralNominalInspection.queries context.state context.interpretation declaration := rfl
  rw [queries]
  rw [inspectMany_local context next view _ bounds (fun _ => none) 0 same]
  rfl

/-- A source-local, finite observation guard. It contains no report equality,
branch semantics, candidate selection, Instance or Evidence premise. -/
def FootprintAt (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (root : GeneralSourceDictionaries.Occurrence roles) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments context root = some bounds →
      ∀ slot ∈ footprints context.state
        (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
        next.nominals slot = context.state.nominals slot

theorem preservesAt_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (same : FootprintAt registry context next root) : PreservesAt registry context next root := by
  intro declaration visible role bounds located
  exact report_local context next view declaration bounds (same declaration visible role bounds located)

/-- Local source Instance transport now needs only finite syntactic observations,
not equality of computed reports. The target state model remains explicit. -/
theorem instance_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : GeneralNominalCommonBridge.Assignment) (root : GeneralSourceDictionaries.Occurrence roles)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (same : FootprintAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children :=
  instance_of_reports registry context next model root key children
    (preservesAt_of_footprint registry context next view root same) valid old

/-- Children are evidenced at the new context, so their descriptors need not be
preserved by this parent-local guard. -/
theorem node_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : GeneralNominalCommonBridge.Assignment) (root : GeneralSourceDictionaries.Occurrence roles)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (same : FootprintAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model)
      children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root
      (.node key dictionaries) :=
  node_of_reports registry context next model root key children dictionaries
    (preservesAt_of_footprint registry context next view root same) valid old given

end Yulang.GeneralDictionaryInspectionLocality
