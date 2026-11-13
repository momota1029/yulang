import Yulang.GeneralNominalBranchingLabels

/-! Nested nominal/pair inspection preserves a forest of actual input
origins, across all positions and all captures in the actual report. -/
namespace Yulang.GeneralNominalCompoundCapturePaths
open GeneralNominalRecursiveInspection GeneralNominalBranchingReadback
open GeneralNominalBranchingCaptures GeneralNominalFiniteMeaning
open GeneralNominalInspection (Query Bounds)

mutual
  def Projectable : Query → Prop
    | .node .pair children => children.length = 2 ∧ ProjectableMany children
    | .node _ _ => False
    | .nominal _ children => ProjectableMany children
    | _ => True
  def ProjectableMany : List Query → Prop
    | [] => True
    | query :: rest => Projectable query ∧ ProjectableMany rest
end

private theorem empty (report : Report state) (none : report.captures = []) : Captures report allowed := by
  intro capture member
  rw [none] at member
  cases member

private theorem append (one : Captures (first : Report state) allowed) (two : Captures (last : Report state) allowed) :
    Captures (first.append last) allowed := by
  intro capture member
  rcases List.mem_append.mp member with member | member
  · exact one capture member
  · exact two capture member

mutual
  theorem inspect_paths (state : GeneralNominalState.State) (query : Query) (fragment : Projectable query)
      (bounds : Bounds state) (origin : Origin) (known : allowed origin)
      (nominalNext : ∀ parent, allowed parent → ∀ name index, allowed (.nominal parent name index))
      (pairNext : ∀ parent, allowed parent → ∀ index : Fin 2, allowed (.structural parent .pair index.val)) :
      Captures (inspect state query bounds (some origin)) allowed := by
    cases query with
    | variables names =>
      intro capture member
      simp only [inspect] at member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      exact ⟨origin,rfl,known⟩
    | deferred => simp only [inspect]; exact empty _ rfl
    | scalar base =>
      simp only [inspect,Report.visit]
      split
      · exact empty _ rfl
      · split
        · split <;> exact empty _ rfl
        · exact empty _ rfl
        · exact empty _ rfl
    | node shape children =>
      cases shape with
      | record | variant | exactEmpty => cases fragment
      | pair =>
        simp only [inspect,Report.visit]
        split
        · split
          · apply many_paths state children fragment.2 _ _ 0
            · intro index bound
              have small : index < 2 := fragment.1 ▸ bound
              exact ⟨_,rfl,by simpa only [Nat.zero_add] using pairNext origin known ⟨index,small⟩⟩
            · exact nominalNext
            · exact pairNext
          · exact empty _ rfl
        · exact empty _ rfl
        · exact empty _ rfl
    | nominal name children =>
      have many (bounds : List (Bounds state)) :
          Captures (inspectMany state children bounds (fun index => some (.nominal origin name index)) 0) allowed :=
        many_paths state children fragment bounds _ 0
          (fun index _ => ⟨_,rfl,by simpa only [Nat.zero_add] using nominalNext origin known name index⟩)
          nominalNext pairNext
      simp only [inspect,Report.visit]
      split
      · split <;> exact empty _ rfl
      · split
        · split
          · exact empty _ rfl
          · split
            · exact many _
            · split
              · exact empty _ rfl
              · split
                · split
                  · exact empty _ rfl
                  · exact append (many _) (many _)
                · exact empty _ rfl
        · exact empty _ rfl
    termination_by sizeOf query

  theorem many_paths (state : GeneralNominalState.State) (queries : List Query) (fragment : ProjectableMany queries)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (known : ∀ index, index < queries.length → ∃ origin, origins (offset+index) = some origin ∧ allowed origin)
      (nominalNext : ∀ parent, allowed parent → ∀ name index, allowed (.nominal parent name index))
      (pairNext : ∀ parent, allowed parent → ∀ index : Fin 2, allowed (.structural parent .pair index.val)) :
      Captures (inspectMany state queries bounds origins offset) allowed := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany] <;> exact empty _ rfl
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany]; exact empty _ rfl
      | cons head tail =>
        simp only [inspectMany]
        apply append
        · obtain ⟨origin,recorded,root⟩ := known 0 (by simp)
          simp only [Nat.add_zero] at recorded
          rw [recorded]
          exact inspect_paths state query fragment.1 head origin root nominalNext pairNext
        · apply many_paths state rest fragment.2 tail origins (offset+1) _ nominalNext pairNext
          intro index bound
          simpa only [Nat.add_assoc,Nat.add_comm 1 index] using known (index+1) (by simp; omega)
    termination_by sizeOf queries
end

def Explained (roots : List (Origin × Tree)) (origin : Origin) : Prop :=
  ∃ root ∈ roots, ∃ depth, Path root.1 depth origin

theorem explained_nominal (known : Explained roots origin) : Explained roots (.nominal origin name index) := by
  obtain ⟨root,member,depth,path⟩ := known
  exact ⟨root,member,depth+1,.nominal path⟩

theorem explained_pair (known : Explained roots origin) (index : Fin 2) :
    Explained roots (.structural origin .pair index.val) := by
  obtain ⟨root,member,depth,path⟩ := known
  exact ⟨root,member,depth+1,.pair index path⟩

theorem report_forest (state : GeneralNominalState.State) (queries : List Query) (fragment : ProjectableMany queries)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin)
    (known : ∀ index, index < queries.length → ∃ origin, origins index = some origin ∧ Explained roots origin) :
    Captures (inspectMany state queries bounds origins 0) (Explained roots) :=
  many_paths state queries fragment bounds origins 0 (by simpa only [Nat.zero_add] using known)
    (fun _ known _ _ => explained_nominal known) (fun _ known index => explained_pair known index)

theorem explained_value {model : GeneralNominalCommonBridge.Assignment}
    (known : Explained roots origin) (meanings : ∀ root ∈ roots, At model .actual root.1 root.2.value)
    (observed : ∃ value, Observes model origin value) :
    ∃ root ∈ roots, ∃ part : Tree, part.mass ≤ root.2.mass ∧ At model .actual origin part.value := by
  obtain ⟨root,member,depth,path⟩ := known
  obtain ⟨value,seen⟩ := observed
  have meaning := meanings root member
  obtain ⟨part,bounded,equal⟩ := observed_path path root.2 meaning.2 seen
  refine ⟨root,member,part,by omega,⟨⟨value,seen⟩,?_⟩⟩
  intro actual observed
  exact approx_left (GeneralNominalBranchingLabels.path_unique path (at_unique meaning) actual value observed seen) equal

theorem simultaneous_captures (packet : GeneralNominalSaturationState.Packet roles)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (roots : List (Origin × Tree))
    (fragment : ProjectableMany (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration))
    (known : ∀ index, index < (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration).length →
      ∃ origin, (packet.site.inputs[index]?).join = some origin ∧ Explained roots origin)
    (meanings : ∀ root ∈ roots, At model .actual root.1 root.2.value)
    (generation : GeneralNominalSharedCaptures.GenerationGuard state packet)
    (arguments : ∀ clause ∈ packet.declaration.requirements,
      GeneralPatternGroundSubstitution.ApplicationArgs clause.arguments) :
    ∃ labels : Nat → Tree, ∀ name, GeneralNominalSharedCaptures.Needed packet name →
      (∃ root ∈ roots, (labels name).mass ≤ root.2.mass) ∧
      GeneralNominalStructuralContainment.CaptureValue packet model name (labels name).value := by
  classical
  have captures := report_forest packet.context.state _ fragment packet.bounds _ known
  have available : ∀ name, GeneralNominalSharedCaptures.Needed packet name → ∃ part : Tree,
      (∃ root ∈ roots, part.mass ≤ root.2.mass) ∧
      GeneralNominalStructuralContainment.CaptureValue packet model name part.value := by
    intro name needed
    obtain ⟨origin,usable⟩ := generation name needed
    obtain ⟨capture,member,_,recorded⟩ := usable.1.1
    obtain ⟨actual,same,explained⟩ := captures capture member
    have identity := Option.some.inj (same.symm.trans recorded)
    subst actual
    obtain ⟨root,present,part,bounded,meaning⟩ := explained_value explained meanings (usable.2 model valid).1
    exact ⟨part,⟨root,present,bounded⟩,GeneralNominalGroundProduction.capture_value packet model valid
      (GeneralNominalBranchingLabels.needed_not_output packet arguments needed) usable meaning⟩
  let labels : Nat → Tree := fun name => if needed : GeneralNominalSharedCaptures.Needed packet name then
    Classical.choose (available name needed) else .scalar .int
  refine ⟨labels,?_⟩
  intro name needed
  simpa only [labels,dite_eq_left needed] using Classical.choose_spec (available name needed)

end Yulang.GeneralNominalCompoundCapturePaths
