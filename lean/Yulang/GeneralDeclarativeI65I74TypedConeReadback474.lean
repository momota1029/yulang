import Yulang.GeneralDeclarativeI65I74OldPhysicalCtorMeaning474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open ObservationSyntax471 (Slot Label ReadsDescription description_exact codeLabel
  readDescription no_duplicate_slots_in_a_description selected_child_at_exact_unique_slot)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleRegularGraph (Node successors)
open QuotientObservation471 (ExactCone ConeWire Wire embedded cone projectNode cone_same_children cone_replay_sound)

theorem map_some_indexes_every_selected_operand (f : α → Option β)
    {input : List α} {output : List β} (all : input.mapM f = some output)
    {a : α} (present : a ∈ input) : ∃ b ∈ output, f a = some b := by
  induction input generalizing output with
  | nil => cases present
  | cons first rest ih =>
    cases g : f first with
    | none => simp [List.mapM_cons,g,bind,Option.bind] at all
    | some next =>
      cases children : rest.mapM f with
      | none => simp [List.mapM_cons,g,children,bind,Option.bind] at all
      | some tail =>
        have outputEq : next :: tail = output := by
          simpa [List.mapM_cons,g,children,bind,Option.bind,pure] using all
        subst output
        rcases List.mem_cons.mp present with head|other
        · subst a
          exact ⟨next,List.mem_cons_self,g⟩
        · obtain ⟨inside,there,known⟩ := ih children other
          exact ⟨inside,List.mem_cons_of_mem _ there,known⟩

theorem scalar_descriptions_have_no_hidden_successors
    {s : GeneralDeclarativeI65.State} {term : Expr} {base fields}
    (d : ReadsDescription s term (.scalar base) fields) : fields = [] := by
  cases d
  rfl

theorem a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors
    {s : GeneralDeclarativeI65.State} {t : Positions n} {i : Fin n}
    (closed : graphOf s t i ≠ .unresolved) :
    ∃ e label children keys,
      readTermAt s t i = some e ∧ ReadsDescription s e label children ∧
      children.mapM (fun c => findPosition t (anchorFor (t.cells.get i) c.1 c.2)) = some keys ∧
      successors (graphOf s t) i = keys := by
  cases expression : readTermAt s t i with
  | none => exact (closed (by simp [graphOf,readNodeAt,expression,bind,Option.bind])).elim
  | some term =>
    cases d : readDescription s term with
    | none => exact (closed (by simp [graphOf,readNodeAt,expression,d,bind,Option.bind])).elim
    | some out =>
      obtain ⟨label,children⟩ := out
      cases childKeys : children.mapM (fun c => findPosition t (anchorFor (t.cells.get i) c.1 c.2)) with
      | none => exact (closed (by simp [graphOf,readNodeAt,expression,d,childKeys,bind,Option.bind])).elim
      | some keys =>
        refine ⟨term,label,children,keys,rfl,description_exact.mp d,childKeys,?_⟩
        cases label with
        | scalar base =>
          have empty := scalar_descriptions_have_no_hidden_successors (description_exact.mp d)
          subst children
          have zero : keys = [] := by simpa using childKeys.symm
          subst keys
          simp [successors,graphOf,readNodeAt,expression,d,codeLabel,bind,Option.bind]
        | nominal tag =>
          simp [successors,graphOf,readNodeAt,expression,d,childKeys,codeLabel,bind,Option.bind]
        | structural sign =>
          by_cases supported : sign ∈ t.signs
          · simp [successors,graphOf,readNodeAt,expression,d,childKeys,codeLabel,bind,Option.bind,supported]
          · exact (closed (by simp [graphOf,readNodeAt,expression,d,childKeys,codeLabel,bind,Option.bind,supported])).elim


open G04FiniteConstructorSemantics473 (Shell)

def shellHead : Shell α → Label
  | .scalar b => .scalar b
  | .pair _ _ => .structural .pair
  | .row fs => .structural (.record (fs.map Prod.fst))
  | .exactEmpty => .structural .exactEmpty
  | .variant tag _ => .structural (.variant tag)
  | .unaryNominal key _ => .nominal key

def shellChildren : Shell α → List α
  | .scalar _ | .exactEmpty => []
  | .pair a b => [a,b]
  | .row fs => fs.map Prod.snd
  | .variant _ a | .unaryNominal _ a => [a]

def encodeShell (signs : List GeneralNormalizedObservation.Shape) (shell : Shell (Fin n)) : Option (Node n) :=
  codeLabel signs (shellHead shell) (shellChildren shell)

theorem shell_of_descriptor_keeps_the_actual_signature_and_successor_order
    {s : GeneralDeclarativeI65.State} {term : Expr} {label : Label} {cs : List (Slot × Expr)}
    (desc : ReadsDescription s term label cs) (child : Slot → α) :
    shellHead (byLabel label child) = label ∧
    shellChildren (byLabel label child) = cs.map (child ∘ Prod.fst) := by
  cases desc <;> simp [shellHead,shellChildren,byLabel,ObservationSyntax471.RecordEntries,List.map_map,Function.comp_def]

theorem code_label_commutes_with_injective_coordinate_map
    (signs : List GeneralNormalizedObservation.Shape) (label : Label)
    (kids : List (Fin k)) (embed : Fin k → Fin n) :
    (codeLabel signs label kids).map (projectNode embed) = codeLabel signs label (kids.map embed) := by
  cases label with
  | scalar | nominal => rfl
  | structural shape =>
    by_cases h : shape ∈ signs <;> simp [codeLabel,h,projectNode]

theorem exact_project_node_is_injective_when_coordinates_are_injective
    {embed : Fin k → Fin n} (inj : ∀ i j, embed i = embed j → i = j) :
    ∀ a b : Node k, projectNode embed a = projectNode embed b → a = b := by
  have reverse {a b : List (Fin k)} (eq : a.map embed = b.map embed) : a = b := by
    induction a generalizing b with
    | nil => cases b <;> simp_all
    | cons a as ih =>
      cases b with
      | nil => cases eq
      | cons b bs =>
        obtain ⟨same,tail⟩ := List.cons.inj eq
        rw [inj _ _ same,ih tail]
  intro a b h
  cases a <;> cases b <;> simp [projectNode] at h ⊢
  all_goals first | exact h | exact ⟨h.1,reverse h.2⟩

theorem exact_map_option_replays_all_literal_children (f : α → Option β)
    (g : α → β) (xs : List α)
    (all : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons first rest ih =>
    simp [all first List.mem_cons_self,ih (fun a yes => all a (List.mem_cons_of_mem _ yes))]

theorem exact_closed_observation_supplies_a_typed_shell_at_each_actual_site
    {s : GeneralDeclarativeI65.State} {t : Positions n} {root : Fin n} {scope : ConeWire n k}
    (exact : ExactCone (graphOf s t) root scope) (i : Fin k) :
    ∃ observation : TypedObservationAt s t (embedded scope) i,
      encodeShell t.signs (byLabel observation.head observation.child) = some (cone scope i) := by
  classical
  have known : graphOf s t (embedded scope i) ≠ .unresolved := by
    rw [exact.2.2.2]
    have closed := exact.2.2.1 i
    cases shape : cone scope i <;> simp_all [projectNode]
  obtain ⟨term,label,cs,keys,read,desc,children,succs⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
  have chooseFor (slot : Slot) (child : Expr) (inList : (slot,child) ∈ cs) :
      ∃ j : Fin k, findPosition t (anchorFor (t.cells.get (embedded scope i)) slot child) = some (embedded scope j) := by
    obtain ⟨target,listed,address⟩ := map_some_indexes_every_selected_operand _ children inList
    rw [←succs,cone_same_children exact] at listed
    obtain ⟨inside,_,rfl⟩ := List.mem_map.mp listed
    exact ⟨inside,address⟩
  let chooseAt (slot : Slot) : Fin k :=
    if seen : ∃ e, (slot,e) ∈ cs then
      Classical.choose (chooseFor slot (Classical.choose seen) (Classical.choose_spec seen))
    else scope.site
  have picks (slot : Slot) (child : Expr) (there : (slot,child) ∈ cs) :
      findPosition t (anchorFor (t.cells.get (embedded scope i)) slot child) =
        some (embedded scope (chooseAt slot)) := by
    have existsHere : ∃ e, (slot,e) ∈ cs := ⟨child,there⟩
    let first := Classical.choose existsHere
    have firstSeen : (slot,first) ∈ cs := Classical.choose_spec existsHere
    have unique := no_duplicate_slots_in_a_description desc
    have exactChild : first = child := (Prod.mk.inj
       (Option.some.inj ((selected_child_at_exact_unique_slot unique firstSeen).symm.trans
         (selected_child_at_exact_unique_slot unique there)))).2
    unfold chooseAt
    rw [dite_eq_left existsHere,← exactChild]
    exact Classical.choose_spec (chooseFor slot first firstSeen)
  let o : TypedObservationAt s t (embedded scope) i := ⟨term,read,label,cs,desc,chooseAt,
    fun slot child h => found_position_is_literal (picks slot child h)⟩
  refine ⟨o,?_⟩
  have decoded := shell_of_descriptor_keeps_the_actual_signature_and_successor_order desc chooseAt
  change encodeShell t.signs (byLabel label chooseAt) = _
  unfold encodeShell
  rw [decoded.1,decoded.2]
  have exactKeys : keys = (cs.map (chooseAt ∘ Prod.fst)).map (embedded scope) := by
    apply Option.some.inj
    rw [←children,List.map_map]
    apply exact_map_option_replays_all_literal_children
    rintro ⟨slot,child⟩ found
    exact picks slot child found
  have readGraph : codeLabel t.signs label keys = some (graphOf s t (embedded scope i)) := by
    have unfolded : graphOf s t (embedded scope i) = (codeLabel t.signs label keys).getD .unresolved := by
      simp [graphOf,readNodeAt,read,description_exact.mpr desc,children,bind,Option.bind]
    cases data : codeLabel t.signs label keys with
    | none => exact (known (by simpa [data] using unfolded)).elim
    | some v => simpa [data] using congrArg some unfolded.symm
  have alias : (codeLabel t.signs label (cs.map (chooseAt ∘ Prod.fst))).map
      (projectNode (embedded scope)) = some (projectNode (embedded scope) (cone scope i)) := by
    rw [code_label_commutes_with_injective_coordinate_map,←exactKeys,readGraph,exact.2.2.2]
  cases result : codeLabel t.signs label (cs.map (chooseAt ∘ Prod.fst)) with
  | none => simp [result] at alias
  | some v =>
    simp only [result,Option.map,Option.some.injEq] at alias
    exact congrArg some (exact_project_node_is_injective_when_coordinates_are_injective exact.2.1 _ _ alias)

theorem successful_quotient_observation_has_one_semantic_regular_value_in_every_old_model
    {s : GeneralDeclarativeI65.State} {t : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n k} {partition : Wire k l} {bit}
    (observed : readAlternatives s t rel root scope partition = some bit) :
    ∃ typed : Fin k → G04FiniteConstructorSemantics473.Shell (Fin k),
      ∀ m : GeneralNominalCommonBridge.Assignment, GeneralDeclarativeHead320.Models s.current.ordinary m →
        ∀ i, CommonNominalFullCarrier.Equivalent (interpretedAt s t m (embedded scope i))
          (G04FiniteConstructorSemantics473.value typed i) := by
  have verified : ExactCone (graphOf s t) root scope := by
    unfold readAlternatives at observed
    split at observed
    · exact (cone_replay_sound observed).1
    · cases observed
  classical
  let witness : ∀ i, TypedObservationAt s t (embedded scope) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site verified i)
  exact ⟨typedBy witness,every_original_model_is_compatible_with_the_same_finite_closed_typed_graph witness⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
