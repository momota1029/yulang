import Yulang.GeneralNominalActualInspectionSteps

/-! Dynamic reports with retained input origins stay inside a finite set of
query-directed paths. The bound uses no pool of endpoint or allocation IDs,
and both sides of a strict interval retain the same supplied actual origin. -/
namespace Yulang.GeneralNominalInheritedPaths
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)

mutual
  def paths (query : Query) (root : Origin) : List Origin :=
    root :: match query with
    | .node shape children => manyPaths children (fun index => .structural root shape index) 0
    | .nominal name children => manyPaths children (fun index => .nominal root name index) 0
    | _ => []
  def manyPaths : List Query → (Nat → Origin) → Nat → List Origin
    | [],_,_ => []
    | query :: rest,origins,index => paths query (origins index) ++ manyPaths rest origins (index+1)
end

def Supported (report : Report state) (origins : List Origin) : Prop :=
  (∀ capture ∈ report.captures, ∃ origin, capture.origin = some origin ∧ origin ∈ origins) ∧
  (∀ entry ∈ report.anchors, entry.1 ∈ origins) ∧ ∀ entry ∈ report.tests, entry.1 ∈ origins

theorem supported_mono (supported : Supported (report : Report state) first) (included : first ⊆ last) :
    Supported report last :=
  ⟨fun capture member => by obtain ⟨origin,equal,present⟩ := supported.1 capture member; exact ⟨origin,equal,included present⟩,
    fun entry member => included (supported.2.1 entry member),
    fun entry member => included (supported.2.2 entry member)⟩

private theorem blank (report : Report state) (captures : report.captures = [])
    (anchors : report.anchors = []) (tests : report.tests = []) : Supported report origins := by
  constructor
  · intro capture member; rw [captures] at member; cases member
  · constructor
    · intro entry member; rw [anchors] at member; cases member
    · intro entry member; rw [tests] at member; cases member

theorem append_same (first : Supported (one : Report state) origins) (last : Supported (two : Report state) origins) :
    Supported (one.append two) origins := by
  constructor
  · intro capture member
    rcases List.mem_append.mp member with member | member
    · exact first.1 capture member
    · exact last.1 capture member
  · constructor
    · intro entry member
      rcases List.mem_append.mp member with member | member
      · exact first.2.1 entry member
      · exact last.2.1 entry member
    · intro entry member
      rcases List.mem_append.mp member with member | member
      · exact first.2.2 entry member
      · exact last.2.2 entry member

theorem append_supported (first : Supported (one : Report state) left) (last : Supported (two : Report state) right) :
    Supported (one.append two) (left ++ right) :=
  append_same (supported_mono first (fun _ member => List.mem_append_left _ member))
    (supported_mono last (fun _ member => List.mem_append_right _ member))

private theorem visited (bounds : Bounds state) (test : Test)
    (supported : Supported (report : Report state) origins) :
    Supported (Report.visit bounds (some root) test report) (root :: origins) := by
  constructor
  · intro capture member
    obtain ⟨origin,equal,present⟩ := supported.1 capture member
    exact ⟨origin,equal,List.mem_cons_of_mem _ present⟩
  · constructor
    · intro entry member
      change entry ∈ (root,bounds) :: report.anchors at member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (supported.2.1 entry member)
    · intro entry member
      change entry ∈ (root,test) :: report.tests at member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (supported.2.2 entry member)

mutual
  theorem inspect_supported (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Origin) :
      Supported (inspect state query bounds (some origin)) (paths query origin) := by
    cases query with
    | variables names =>
      simp only [inspect]
      constructor
      · intro capture member
        obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
        exact ⟨origin,rfl,List.mem_cons_self ..⟩
      · constructor
        · intro entry member
          change entry ∈ [(origin,bounds)] at member
          cases List.mem_singleton.mp member
          exact List.mem_cons_self ..
        · intro entry member; cases member
    | deferred source => simpa only [inspect] using blank (block bounds) rfl rfl rfl
    | scalar base =>
      simp only [inspect,paths]
      apply visited
      split
      · exact blank _ rfl rfl rfl
      · split
        · split <;> exact blank _ rfl rfl rfl
        · exact blank _ rfl rfl rfl
        · exact blank _ rfl rfl rfl
    | node shape children =>
      simp only [inspect,paths]
      apply visited
      split
      · split
        · exact many_supported state children _ _ 0
        · exact blank _ rfl rfl rfl
      · exact blank _ rfl rfl rfl
      · exact blank _ rfl rfl rfl
    | nominal name children =>
      simp only [inspect,paths]
      apply visited
      split
      · split <;> exact blank _ rfl rfl rfl
      · split
        · split
          · exact blank _ rfl rfl rfl
          · split
            · exact many_supported state children _ _ 0
            · split
              · exact blank _ rfl rfl rfl
              · split
                · split
                  · exact blank _ rfl rfl rfl
                  · exact append_same (many_supported state children _ _ 0) (many_supported state children _ _ 0)
                · exact blank _ rfl rfl rfl
        · exact blank _ rfl rfl rfl
  termination_by sizeOf query

  theorem many_supported (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Origin) (index : Nat) :
      Supported (inspectMany state queries bounds (fun position => some (origins position)) index)
        (manyPaths queries origins index) := by
    cases queries with
    | nil => cases bounds <;> simpa only [inspectMany] using blank (state := state) _ rfl rfl rfl
    | cons query rest =>
      cases bounds with
      | nil => simpa only [inspectMany] using blank (state := state) _ rfl rfl rfl
      | cons head tail =>
        simp only [inspectMany,manyPaths]
        exact append_supported (inspect_supported state query head (origins index))
          (many_supported state rest tail origins (index+1))
  termination_by sizeOf queries
end

theorem many_congr (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (first last : Nat → Option Origin) (index : Nat)
    (equal : ∀ position, index ≤ position → position < index + queries.length → first position = last position) :
    inspectMany state queries bounds first index = inspectMany state queries bounds last index := by
  induction queries generalizing bounds index with
  | nil => cases bounds <;> simp [inspectMany]
  | cons query rest ih =>
    cases bounds with
    | nil => simp [inspectMany]
    | cons head tail =>
      simp only [inspectMany]
      rw [equal index (Nat.le_refl _) (by simp)]
      rw [ih tail (index+1) (by intro position lower upper; apply equal position <;> simp only [List.length_cons] at * <;> omega)]

theorem inherited_supported (packet : GeneralNominalSaturationState.Packet roles)
    (origins : Nat → Origin)
    (retained : ∀ index, index < (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration).length →
      (packet.site.inputs[index]?).join = some (origins index)) :
    Supported (GeneralNominalSharedCaptures.inheritedReport packet)
      (manyPaths (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration) origins 0) := by
  unfold GeneralNominalSharedCaptures.inheritedReport
  rw [many_congr _ _ _ _ (fun index => some (origins index)) 0 (by
    intro index lower upper; exact retained index (by simpa only [Nat.zero_add] using upper))]
  exact many_supported ..

theorem actual_supported (state : GeneralNominalSaturationState.State roles)
    (packet : GeneralNominalSaturationState.Packet roles) (origins : Nat → Origin)
    (retained : ∀ index, index < (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration).length →
      ((GeneralNominalFeedbackSites.recover state packet.site).inputs[index]?).join = some (origins index)) :
    Supported (GeneralNominalActualInspectionSteps.inspection state packet)
      (manyPaths (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration) origins 0) := by
  unfold GeneralNominalActualInspectionSteps.inspection
  rw [many_congr _ _ _ _ (fun index => some (origins index)) 0 (by
    intro index lower upper; exact retained index (by simpa only [Nat.zero_add] using upper))]
  exact many_supported ..

end Yulang.GeneralNominalInheritedPaths
