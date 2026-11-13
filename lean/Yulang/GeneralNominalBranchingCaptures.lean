import Yulang.GeneralNominalBranchingReadback

/-! Direct constructor captures are real one-edge input projections, for
arbitrary refreshed intervals and either nominal endpoint inspection. -/
namespace Yulang.GeneralNominalBranchingCaptures
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)
open GeneralNominalBranchingReadback

def Captures (report : Report state) (allowed : Origin → Prop) : Prop :=
  ∀ capture ∈ report.captures, ∃ origin, capture.origin = some origin ∧ allowed origin

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

theorem variables_many (state : GeneralNominalState.State) (names : List Nat)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (known : ∀ index, index < names.length → ∃ origin, origins (offset+index) = some origin ∧ allowed origin) :
    Captures (inspectMany state (names.map fun name => .variables [name]) bounds origins offset) allowed := by
  induction names generalizing bounds offset with
  | nil => cases bounds <;> simp only [List.map_nil,inspectMany] <;> exact empty _ rfl
  | cons name rest ih =>
    cases bounds with
    | nil => simp only [List.map_cons,inspectMany]; exact empty _ rfl
    | cons head tail =>
      simp only [List.map_cons,inspectMany]
      apply append
      · intro capture member
        have same : capture = ⟨name,head,origins offset⟩ := by simpa only [inspect,List.map_cons,List.map_nil,List.mem_singleton] using member
        subst capture
        simpa only [Nat.add_zero] using known 0 (by simp)
      · apply ih
        intro index bound
        simpa only [Nat.add_assoc,Nat.add_comm 1 index] using known (index+1) (by simp; omega)

theorem nominal (state : GeneralNominalState.State) (name : Nat) (names : List Nat)
    (bounds : Bounds state) (origin : Origin) :
    Captures (inspect state (.nominal name (names.map fun name => .variables [name])) bounds (some origin))
      (Path origin 1) := by
  have many (bounds : List (Bounds state)) :
      Captures (inspectMany state (names.map fun name => .variables [name]) bounds
        (fun index => some (.nominal origin name index)) 0) (Path origin 1) :=
    variables_many state names bounds (fun index => some (.nominal origin name index)) 0
      (fun index _ => ⟨_,rfl,.nominal .root⟩)
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

theorem pair (state : GeneralNominalState.State) (first last : Nat)
    (bounds : Bounds state) (origin : Origin) :
    Captures (inspect state (.node .pair [.variables [first],.variables [last]]) bounds (some origin))
      (Path origin 1) := by
  simp only [inspect,Report.visit]
  split
  · split
    · apply variables_many state [first,last]
      intro index bound
      exact ⟨_,rfl,by simpa only [Nat.zero_add] using (Path.pair (root := origin) ⟨index,bound⟩ .root)⟩
    · exact empty _ rfl
  · exact empty _ rfl
  · exact empty _ rfl

def QueryShape : Query → Prop
  | .nominal _ children => ∃ names : List Nat, children = names.map (fun name => .variables [name])
  | .node .pair children => ∃ first last, children = [.variables [first],.variables [last]]
  | _ => False

theorem single_capture (state : GeneralNominalState.State) (query : Query) (shape : QueryShape query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (recorded : origins 0 = some origin) :
    Captures (inspectMany state [query] bounds origins 0) (Path origin 1) := by
  cases bounds with
  | nil => simp only [inspectMany]; exact empty _ rfl
  | cons head tail =>
    simp only [inspectMany]
    apply append
    · rw [recorded]
      cases query with
      | variables | scalar | deferred => cases shape
      | nominal name children =>
        obtain ⟨names,rfl⟩ := shape
        exact nominal state name names head origin
      | node structural children =>
        cases structural with
        | pair =>
          obtain ⟨first,last,rfl⟩ := shape
          exact pair state first last head origin
        | record | variant | exactEmpty => cases shape
    · cases tail <;> simp only [inspectMany] <;> exact empty _ rfl

theorem usable_path (packet : GeneralNominalSaturationState.Packet roles)
    (queries : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = [query])
    (shape : QueryShape query) (recorded : packet.site.inputs[0]? = some (some origin))
    (usable : GeneralNominalSharedCaptures.Usable packet name actual) : Path origin 1 actual := by
  obtain ⟨capture,member,_,retained⟩ := usable.1.1
  unfold GeneralNominalSharedCaptures.inheritedReport at member
  rw [queries] at member
  obtain ⟨chosen,same,path⟩ := single_capture packet.context.state query shape packet.bounds
    (fun index => (packet.site.inputs[index]?).join)
    (by rw [recorded]; rfl) capture member
  have equal := Option.some.inj (same.symm.trans retained)
  exact equal ▸ path

theorem path_trans (first : Path root a middle) (last : Path middle b endpoint) : Path root (a+b) endpoint := by
  induction last with
  | root => simpa only [Nat.add_zero] using first
  | nominal prior ih => exact .nominal ih
  | pair index prior ih => exact .pair index ih

end Yulang.GeneralNominalBranchingCaptures
