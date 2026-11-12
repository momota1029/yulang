import Yulang.GeneralNominalSpineFacts

/-! Independent binary nominal branches. Cross-branch capture separation is a
syntactic name condition, never an assumption of the desired projection model. -/
namespace Yulang.GeneralNominalBranchProjection
open GeneralNominalRecursiveInspection GeneralNominalSpineFacts
open CommonNominalFullCarrier

theorem point_argument_matches (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (slot child : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (index : Nat)
    (found : descriptor.arguments[index]? = some (.type (child,child)))
    (origin : Origin) (consistent : Matches state model slot origin) :
    Matches state model child (.nominal origin descriptor.declaration.name index) := by
  have arg := nominal_argument_bounds state model valid slot descriptor recorded index (child,child) found
  have transport := nominal_observation_iff state model slot origin consistent descriptor.declaration.name index
  exact ⟨by obtain ⟨a,ha⟩ := arg.1; exact ⟨a,(transport a).mpr ha⟩,
    fun a ha => ⟨(arg.2 a ((transport a).mp ha)).2,(arg.2 a ((transport a).mp ha)).1⟩⟩

theorem append_projection (state : GeneralNominalState.State) (left right : Report state)
    (model : GeneralNominalCommonBridge.Assignment)
    (one : ProjectionModels state left model) (two : ProjectionModels state right model)
    (separate : ∀ a ∈ left.captures, ∀ b ∈ right.captures, a.name ≠ b.name) :
    ProjectionModels state (left.append right) model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a member
    rcases List.mem_append.mp member with h | h
    · exact one.1 a h
    · exact two.1 a h
  · intro a member
    rcases List.mem_append.mp member with h | h
    · exact one.2.1 a h
    · exact two.2.1 a h
  · intro a ha b hb same
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact one.2.2.1 a ha b hb same
    · exact (separate a ha b hb same).elim
    · exact (separate b hb a ha same.symm).elim
    · exact two.2.2.1 a ha b hb same
  · intro a ha b hb same
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact one.2.2.2 a ha b hb same
    · exact (separate a ha b hb same).elim
    · exact (separate b hb a ha same.symm).elim
    · exact two.2.2.2 a ha b hb same

theorem spine_capture_name (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine state names bounds slot) (origin : Option Origin)
    (capture : Capture state) (member : capture ∈ (inspect state spine.query (slot,slot) origin).captures) :
    ∃ i, capture.name = names i := by
  induction spine generalizing origin with
  | leaf slot descriptor recorded parameters =>
    rw [Spine.query,inspect_leaf state names bounds slot descriptor recorded parameters] at member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact ⟨i,rfl⟩
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Spine.query,inspect_wrap state slot child descriptor recorded parameters] at member
    exact ih _ member


theorem inspect_fork (state : GeneralNominalState.State)
    (slot left right : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
    (one two : GeneralNominalInspection.Query) (origin : Option Origin) :
    inspect state (.nominal descriptor.declaration.name [one,two]) (slot,slot) origin =
    Report.visit (slot,slot) origin (.nominal descriptor.declaration.name 2)
      ((inspect state one (left,left)
        (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 0))).append
       (inspect state two (right,right)
        (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 1)))) := by
  have args : typeArguments descriptor.arguments = some [(left,left),(right,right)] := by rw [parameters]; rfl
  simp only [inspect,recorded,args,↓reduceIte,inspectMany,append_empty,List.length_cons,List.length_nil]

/-- Two independently deep finite nominal spines may branch below one parent.
All projection constraints follow in the same source model; cross-branch
sharing is excluded by disjoint binder names, not by assumed semantics. -/
theorem fork_projection (state : GeneralNominalState.State)
    {n m : Nat} (names : Fin n → Nat) (other : Fin m → Nat)
    (distinct : Function.Injective names) (otherDistinct : Function.Injective other)
    (separate : ∀ i j, names i ≠ other j) (bounds otherBounds)
    (slot left right : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
    (one : Spine state names bounds left) (two : Spine state other otherBounds right)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin) (consistent : ∀ o, origin = some o → Matches state model slot o) :
    ProjectionModels state (inspect state (.nominal descriptor.declaration.name [one.query,two.query])
      (slot,slot) origin) model := by
  rw [inspect_fork state slot left right descriptor recorded parameters]
  apply visit_models state model valid slot descriptor recorded 2 (by rw [parameters]; rfl) origin consistent
  apply append_projection
  · apply spine_projection state names distinct bounds one model valid
    intro o eq; cases Option.some.inj eq
    exact point_argument_matches state model valid slot left descriptor recorded 0
      (by rw [parameters]; rfl) _ (origin_default state model slot origin consistent)
  · apply spine_projection state other otherDistinct otherBounds two model valid
    intro o eq; cases Option.some.inj eq
    exact point_argument_matches state model valid slot right descriptor recorded 1
      (by rw [parameters]; rfl) _ (origin_default state model slot origin consistent)
  · intro a ha b hb same
    obtain ⟨i,hi⟩ := spine_capture_name state names bounds one _ a ha
    obtain ⟨j,hj⟩ := spine_capture_name state other otherBounds two _ b hb
    exact separate i j (hi.symm.trans (same.trans hj))


theorem fork_finished (state : GeneralNominalState.State) {n m : Nat}
    (names : Fin n → Nat) (other : Fin m → Nat) (bounds otherBounds)
    (slot left right : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
    (one : Spine state names bounds left) (two : Spine state other otherBounds right) (origin : Option Origin) :
    Finished (inspect state (.nominal descriptor.declaration.name [one.query,two.query]) (slot,slot) origin) := by
  rw [inspect_fork state slot left right descriptor recorded parameters]
  have a := spine_finished state names bounds one (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 0))
  have b := spine_finished state other otherBounds two (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 1))
  exact ⟨by simp only [Report.visit,Report.append,a.1,b.1,List.nil_append],
    by simp only [Report.visit,Report.append,a.2.1,b.2.1,List.nil_append],
    by simp only [Report.visit,Report.append,a.2.2,b.2.2,List.nil_append]⟩

theorem fork_bindings (state : GeneralNominalState.State) {n m : Nat}
    (names : Fin (n+m) → Nat) (bounds : Fin (n+m) → GeneralNominalInspection.Bounds state)
    (slot left right : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
    (one : Spine state (fun i : Fin n => names (i.castAdd m)) (fun i => bounds (i.castAdd m)) left)
    (two : Spine state (fun i : Fin m => names (i.natAdd n)) (fun i => bounds (i.natAdd n)) right)
    (origin : Option Origin) :
    bindings state (inspect state (.nominal descriptor.declaration.name [one.query,two.query]) (slot,slot) origin) =
      List.ofFn fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2) := by
  rw [inspect_fork state slot left right descriptor recorded parameters]
  change List.map _ (_ ++ _) = _
  rw [List.map_append]
  rw [← bindings,← bindings,spine_bindings,spine_bindings,List.ofFn_add]
  rfl


theorem fork_checked (state : GeneralNominalState.State) {n m : Nat}
    (names : Fin n → Nat) (other : Fin m → Nat) (bounds otherBounds)
    (slot left right : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
    (one : Spine state names bounds left) (two : Spine state other otherBounds right)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin) :
    ∀ pair ∈ (inspect state (.nominal descriptor.declaration.name [one.query,two.query]) (slot,slot) origin).checked,
      Subtype (model (state.base.source pair.1)).1 (model (state.base.source pair.2)).1 := by
  rw [inspect_fork state slot left right descriptor recorded parameters]
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · exact subtype_refl _
  · rcases List.mem_append.mp member with a | b
    · exact spine_checked state names bounds one model valid _ pair a
    · exact spine_checked state other otherBounds two model valid _ pair b

end Yulang.GeneralNominalBranchProjection
