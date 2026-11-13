import Yulang.GeneralNominalHoleReadback

/-! A finite origin frontier for direct structural and point-nominal paths.
Only inspected parents must pass K2; a terminal cyclic value stays opaque. -/
namespace Yulang.GeneralNominalSourceFrontier
open GeneralNominalRecursiveInspection GeneralNominalCycleK2

inductive Label where
  | structural (shape : GeneralNormalizedObservation.Shape) (index : Nat)
  | nominal (name index : Nat)
  deriving DecidableEq

def Label.apply : Label → Origin → Origin
  | .structural shape index,root => .structural root shape index
  | .nominal name index,root => .nominal root name index

def structuralChildren (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    List (Label × Fin state.base.slots) :=
  match state.view.heads slot with
  | .structural kind children => List.ofFn fun index =>
      (.structural (state.view.shapes kind) index.val,children index)
  | _ => []

def nominalChildren (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    List (Label × Fin state.base.slots) :=
  match state.nominals slot with
  | none => []
  | some descriptor => (List.ofFn fun index : Fin descriptor.arguments.length =>
      match descriptor.arguments[index] with
      | .type (lower,upper) => if lower = upper then some (.nominal descriptor.declaration.name index.val,lower) else none
      | .row _ => none).filterMap id

def children (state : GeneralNominalState.State) (slot : Fin state.base.slots) :=
  structuralChildren state slot ++ nominalChildren state slot

theorem child_direct (member : (label,last) ∈ children state first) : DirectEdge state first last := by
  rcases List.mem_append.mp member with structural | nominal
  · unfold structuralChildren at structural
    split at structural
    · rename_i kind values recorded
      obtain ⟨index,equal⟩ := List.mem_ofFn.mp structural
      cases equal
      exact Or.inl ⟨kind,values,recorded,index,rfl⟩
    · cases structural
  · unfold nominalChildren at nominal
    split at nominal
    · cases nominal
    · rename_i descriptor recorded
      obtain ⟨value,present,equal⟩ := List.mem_filterMap.mp nominal
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
      dsimp only [id] at equal
      split at equal
      · rename_i lower upper found
        split at equal
        · rename_i same
          cases equal
          refine Or.inr ⟨descriptor,recorded,index.val,?_⟩
          rw [List.getElem?_eq_getElem index.isLt]
          exact congrArg some (found.trans (by rw [same]))
        · cases equal
      · cases equal

inductive Walk (state : GeneralNominalState.State) :
    Fin state.base.slots → Origin → List (Fin state.base.slots) → Fin state.base.slots → Origin → Prop
  | stop (slot root) : Walk state slot root [] slot root
  | next : (label,middle) ∈ children state first → ¬ RecursAt state first →
      Walk state middle (label.apply root) inspected last result →
      Walk state first root (first :: inspected) last result

theorem walk_path (walk : Walk state first root inspected last result) : DirectPath state first last := by
  induction walk with
  | stop => exact .nil _
  | next edge safe walk ih => exact .cons (child_direct edge) ih

theorem walk_reaches (walk : Walk state first root inspected last result)
    (member : slot ∈ inspected ++ [last]) : DirectPath state first slot := by
  induction walk with
  | stop => cases List.mem_singleton.mp member; exact .nil _
  | next edge safe walk ih =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact .nil _
      · exact .cons (child_direct edge) (ih member)

theorem walk_distinct (walk : Walk state first root inspected last result) : (inspected ++ [last]).Nodup := by
  induction walk with
  | stop => simp
  | next edge safe walk ih =>
      refine List.nodup_cons.mpr ⟨?_,ih⟩
      intro member
      exact safe (Or.inl ⟨_,child_direct edge,walk_reaches walk member⟩)

theorem walk_length (walk : Walk state first root inspected last result) : inspected.length < state.base.slots := by
  have bound := (walk_distinct walk).length_le_of_subset
    (show inspected ++ [last] ⊆ List.finRange state.base.slots from fun _ _ => List.mem_finRange _)
  simp only [List.length_append,List.length_singleton,List.length_finRange] at bound
  omega

def explore (state : GeneralNominalState.State) : Nat → Fin state.base.slots → Origin → List Origin
  | 0,_,root => [root]
  | fuel+1,slot,root => root :: (children state slot).flatMap fun next => explore state fuel next.2 (next.1.apply root)

theorem explored (walk : Walk state first root inspected last result) (enough : inspected.length ≤ fuel) :
    result ∈ explore state fuel first root := by
  induction walk generalizing fuel with
  | stop => cases fuel <;> simp [explore]
  | next edge safe walk ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,edge,ih (by simpa using enough)⟩)

def frontier (state : GeneralNominalState.State) : List Origin :=
  (GeneralNominalState.sources state).map Origin.source ++
    (List.finRange state.base.slots).flatMap fun slot =>
      explore state state.base.slots slot (.source (state.base.source slot))

theorem source_member (member : identity ∈ GeneralNominalState.sources state) : Origin.source identity ∈ frontier state :=
  List.mem_append_left _ (List.mem_map.mpr ⟨identity,member,rfl⟩)

theorem frontier_covers (walk : Walk state first (.source (state.base.source first)) inspected last result) :
    result ∈ frontier state :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨first,List.mem_finRange _,explored walk (Nat.le_of_lt (walk_length walk))⟩)

theorem cycle_stops (cycle : RecursAt state first)
    (walk : Walk state first root inspected last result) : inspected = [] ∧ result = root := by
  cases walk with
  | stop => exact ⟨rfl,rfl⟩
  | next edge safe rest => exact False.elim (safe cycle)

theorem initial_inputs {roles : Roles.RoleDecls} {root : GeneralSourceDictionaries.Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (index : Fin (roles root.demand.role).arity) :
    Origin.source (root.demand.arguments index).1 ∈ frontier context.state ∧
      Origin.source (root.demand.arguments index).2 ∈ frontier context.state :=
  ⟨source_member (source.linked.1 index).1,source_member (source.linked.1 index).2⟩

end Yulang.GeneralNominalSourceFrontier
