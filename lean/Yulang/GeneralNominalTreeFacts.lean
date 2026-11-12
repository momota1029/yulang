import Yulang.GeneralNominalBranchFacts

/-! Arbitrary finite binary nominal trees with point internal edges and globally
linear binder leaves. The certificate contains only source syntax and lookup
facts; it does not contain model validity or candidate-private conclusions. -/
namespace Yulang.GeneralNominalTreeFacts
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralNominalSpineFacts GeneralNominalBranchProjection
open GeneralNominalLinearCaptureFacts CommonNominalFullCarrier

inductive Tree (state : GeneralNominalState.State) : {n : Nat} →
    (Fin n → Nat) → (Fin n → GeneralNominalInspection.Bounds state) → Fin state.base.slots → Type where
  | leaf {n} (names : Fin n → Nat) (bounds) (slot)
      (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i)) : Tree state names bounds slot
  | wrap {n names bounds} (slot child)
      (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = [.type (child,child)])
      (rest : @Tree state n names bounds child) : Tree state names bounds slot
  | fork {n m} (names : Fin (n+m) → Nat) (bounds) (slot left right)
      (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
      (one : Tree state (fun i : Fin n => names (i.castAdd m)) (fun i => bounds (i.castAdd m)) left)
      (two : Tree state (fun i : Fin m => names (i.natAdd n)) (fun i => bounds (i.natAdd n)) right) :
      Tree state names bounds slot

def Tree.query {state n names bounds slot} : @Tree state n names bounds slot → GeneralNominalInspection.Query
  | .leaf names _ _ descriptor _ _ => .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])
  | .wrap _ _ descriptor _ _ rest => .nominal descriptor.declaration.name [rest.query]
  | .fork _ _ _ _ _ descriptor _ _ one two => .nominal descriptor.declaration.name [one.query,two.query]

theorem capture_name (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot) (origin : Option Origin)
    (capture : Capture state) (member : capture ∈ (inspect state tree.query (slot,slot) origin).captures) :
    ∃ i, capture.name = names i := by
  induction tree generalizing origin with
  | leaf names bounds slot descriptor recorded parameters =>
    rw [Tree.query,inspect_leaf state names bounds slot descriptor recorded parameters] at member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact ⟨i,rfl⟩
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Tree.query,inspect_wrap state slot child descriptor recorded parameters] at member
    exact ih _ member
  | fork names bounds slot left right descriptor recorded parameters one two ihOne ihTwo =>
    rw [Tree.query,inspect_fork state slot left right descriptor recorded parameters] at member
    rcases List.mem_append.mp member with ha | hb
    · obtain ⟨i,hi⟩ := ihOne _ ha
      exact ⟨i.castAdd _,hi⟩
    · obtain ⟨i,hi⟩ := ihTwo _ hb
      exact ⟨i.natAdd _,hi⟩

theorem tree_projection (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot) (distinct : Function.Injective names)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin) (consistent : ∀ o, origin = some o → Matches state model slot o) :
    ProjectionModels state (inspect state tree.query (slot,slot) origin) model := by
  induction tree generalizing origin with
  | leaf names bounds slot descriptor recorded parameters =>
    rw [Tree.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    exact visit_models state model valid slot descriptor recorded _ (by rw [parameters]; exact List.length_ofFn)
      origin consistent _ (variables_models state model valid slot descriptor recorded names distinct bounds parameters _
        (origin_default state model slot origin consistent))
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Tree.query,inspect_wrap state slot child descriptor recorded parameters]
    apply visit_models state model valid slot descriptor recorded 1 (by rw [parameters]; rfl) origin consistent
    apply ih distinct
    intro o eq; cases Option.some.inj eq
    exact point_child_matches state model valid slot child descriptor recorded parameters _
      (origin_default state model slot origin consistent)
  | @fork n m names bounds slot left right descriptor recorded parameters one two ihOne ihTwo =>
    rw [Tree.query,inspect_fork state slot left right descriptor recorded parameters]
    apply visit_models state model valid slot descriptor recorded 2 (by rw [parameters]; rfl) origin consistent
    have leftDistinct : Function.Injective (fun i : Fin n => names (i.castAdd m)) := by
      intro i j h
      have eq := congrArg Fin.val (distinct h)
      exact Fin.ext eq
    have rightDistinct : Function.Injective (fun i : Fin m => names (i.natAdd n)) := by
      intro i j h
      apply Fin.ext
      have eq := congrArg Fin.val (distinct h)
      simp only [Fin.val_natAdd] at eq
      omega
    apply append_projection
    · apply ihOne leftDistinct
      intro o eq; cases Option.some.inj eq
      exact point_argument_matches state model valid slot left descriptor recorded 0
        (by rw [parameters]; rfl) _ (origin_default state model slot origin consistent)
    · apply ihTwo rightDistinct
      intro o eq; cases Option.some.inj eq
      exact point_argument_matches state model valid slot right descriptor recorded 1
        (by rw [parameters]; rfl) _ (origin_default state model slot origin consistent)
    · intro a ha b hb same
      obtain ⟨i,hi⟩ := capture_name state one _ a ha
      obtain ⟨j,hj⟩ := capture_name state two _ b hb
      have eq := congrArg Fin.val (distinct (hi.symm.trans (same.trans hj)))
      simp only [Fin.val_castAdd,Fin.val_natAdd] at eq
      omega

theorem tree_bindings (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot) (origin : Option Origin) :
    bindings state (inspect state tree.query (slot,slot) origin) =
      List.ofFn fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2) := by
  induction tree generalizing origin with
  | leaf names bounds slot descriptor recorded parameters =>
    rw [Tree.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    simp [bindings,Report.visit,variablesReport,List.map_ofFn,Function.comp_def]
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Tree.query,inspect_wrap state slot child descriptor recorded parameters]
    exact ih _
  | fork names bounds slot left right descriptor recorded parameters one two ihOne ihTwo =>
    rw [Tree.query,inspect_fork state slot left right descriptor recorded parameters]
    change List.map _ (_ ++ _) = _
    rw [List.map_append,← bindings,← bindings,ihOne,ihTwo,List.ofFn_add]
    rfl

theorem tree_finished (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot) (origin : Option Origin) :
    Finished (inspect state tree.query (slot,slot) origin) := by
  induction tree generalizing origin with
  | leaf names bounds slot descriptor recorded parameters =>
    rw [Tree.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    exact ⟨rfl,rfl,rfl⟩
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Tree.query,inspect_wrap state slot child descriptor recorded parameters]
    exact ih _
  | fork names bounds slot left right descriptor recorded parameters one two ihOne ihTwo =>
    rw [Tree.query,inspect_fork state slot left right descriptor recorded parameters]
    have a := ihOne (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 0))
    have b := ihTwo (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 1))
    exact ⟨by simp only [Report.visit,Report.append,a.1,b.1,List.nil_append],
      by simp only [Report.visit,Report.append,a.2.1,b.2.1,List.nil_append],
      by simp only [Report.visit,Report.append,a.2.2,b.2.2,List.nil_append]⟩

theorem tree_bounds (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) :
    ∀ i, Subtype (model (state.base.source (bounds i).1)).1 (model (state.base.source (bounds i).2)).1 := by
  induction tree with
  | leaf names bounds slot descriptor recorded parameters =>
    intro i
    have arg := nominal_argument_bounds state model valid slot descriptor recorded i.val (bounds i)
      (by rw [parameters]; simp [i.isLt])
    obtain ⟨a,ha⟩ := arg.1
    exact subtype_trans (arg.2 a ha).1 (arg.2 a ha).2
  | wrap _ _ _ _ _ _ ih => exact ih
  | fork _ _ _ _ _ _ _ _ _ _ ihOne ihTwo =>
    intro i
    exact Fin.addCases ihOne ihTwo i

theorem tree_checked (state : GeneralNominalState.State) {n names bounds slot}
    (tree : @Tree state n names bounds slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin) :
    ∀ pair ∈ (inspect state tree.query (slot,slot) origin).checked,
      Subtype (model (state.base.source pair.1)).1 (model (state.base.source pair.2)).1 := by
  induction tree generalizing origin with
  | leaf names bounds slot descriptor recorded parameters =>
    rw [Tree.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact subtype_refl _
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp tail
      exact tree_bounds state (.leaf names bounds slot descriptor recorded parameters) model valid i
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Tree.query,inspect_wrap state slot child descriptor recorded parameters]
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact subtype_refl _
    · exact ih _ pair tail
  | fork names bounds slot left right descriptor recorded parameters one two ihOne ihTwo =>
    rw [Tree.query,inspect_fork state slot left right descriptor recorded parameters]
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact subtype_refl _
    · rcases List.mem_append.mp tail with a | b
      · exact ihOne _ pair a
      · exact ihTwo _ pair b

theorem report_exact (context : Context) (declaration : Declaration) {n names bounds slot}
    (tree : @Tree context.state n names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query]) :
    report context declaration [(slot,slot)] =
      { inspect context.state tree.query (slot,slot) none with
        checked := (slot,slot) :: (inspect context.state tree.query (slot,slot) none).checked } := by
  simp [report,query,inspectMany,append_empty]

theorem private_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names) (bounds) {slot}
    (tree : Tree context.state names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query])
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have computed := report_exact context declaration tree query
  have captured : bindings context.state (report context declaration [(slot,slot)]) =
      List.ofFn fun i => (names i,context.state.base.source (bounds i).1,context.state.base.source (bounds i).2) := by
    rw [computed]
    exact tree_bindings context.state tree none
  constructor
  · unfold privateState
    rw [captured]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · exact propagated_models context.state registry root.identity declaration names distinct inputs bounds model valid
        (tree_bounds context.state tree model valid)
    · intro atom member
      obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
      rw [computed] at present
      rcases List.mem_cons.mp present with rfl | tail
      · exact subtype_refl _
      · exact tree_checked context.state tree model valid none pair tail
  · rw [computed]
    exact tree_projection context.state tree distinct model valid none (by intro o eq; cases eq)

/-- Existing finite spines embed without changing any source or query. -/
def ofSpine {state n names bounds slot} : @Spine state n names bounds slot → Tree state names bounds slot
  | .leaf slot descriptor recorded parameters => .leaf names bounds slot descriptor recorded parameters
  | .wrap slot child descriptor recorded parameters rest => .wrap slot child descriptor recorded parameters (ofSpine rest)

theorem ofSpine_query {state n names bounds slot} (spine : @Spine state n names bounds slot) :
    (ofSpine spine).query = spine.query := by
  induction spine with
  | leaf => rfl
  | wrap _ _ _ _ _ _ ih => simp [ofSpine,Tree.query,Spine.query,ih]

/-- The former single-fork class is a special case, not a competing semantics. -/
def ofFork {state n m names bounds slot} (fork : GeneralNominalBranchFacts.Fork state n m names bounds slot) :
    Tree state names bounds slot :=
  .fork names bounds slot fork.left fork.right fork.descriptor fork.recorded fork.parameters
    (ofSpine fork.one) (ofSpine fork.two)

theorem ofFork_query {state n m names bounds slot} (fork : GeneralNominalBranchFacts.Fork state n m names bounds slot) :
    (ofFork fork).query = fork.query := by
  simp [ofFork,Tree.query,GeneralNominalBranchFacts.Fork.query,ofSpine_query]
end Yulang.GeneralNominalTreeFacts
