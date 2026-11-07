import Yulang.CommonSyntax

/-! Finite closed supports for the concrete regular syntax. -/

namespace Yulang.CommonLegacyGraphSupport

universe u v w

def Closed (next : Index → List Index) (states : List Index) : Prop :=
  ∀ state ∈ states, ∀ child ∈ next state, child ∈ states

def FiniteAt (next : Index → List Index) (root : Index) : Prop :=
  ∃ states : List Index, root ∈ states ∧ Closed next states

/-- A finite cluster with already finitely supported outgoing leaves also
has finite support. No bound on numeric state names is assumed. -/
theorem finite_extension {Index : Type u} (next : Index → List Index)
    (roots leaves : List Index)
    (edges : ∀ state ∈ roots, ∀ child ∈ next state, child ∈ roots ∨ child ∈ leaves)
    (supported : ∀ state ∈ leaves, FiniteAt next state) :
    ∀ state ∈ roots, FiniteAt next state := by
  classical
  let support (state : Index) : List Index :=
    if member : state ∈ leaves then Classical.choose (supported state member) else []
  have properties (state : Index) (member : state ∈ leaves) :
      state ∈ support state ∧ Closed next (support state) := by
    simpa only [support, dite_eq_left member] using Classical.choose_spec (supported state member)
  let all := roots ++ leaves.flatMap support
  have leafIncluded (state : Index) (member : state ∈ leaves) : state ∈ all :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨state, member, (properties state member).1⟩)
  intro root member
  refine ⟨all, List.mem_append_left _ member, ?_⟩
  intro state included child childMember
  rcases List.mem_append.mp included with own | external
  · rcases edges state own child childMember with own | external
    · exact List.mem_append_left _ own
    · exact leafIncluded child external
  · obtain ⟨leaf, leafMember, stateMember⟩ := List.mem_flatMap.mp external
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨leaf, leafMember, (properties leaf leafMember).2 state stateMember child childMember⟩)

def refs : CommonSyntax.Layer Row Index → List Index
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => []
  | .union first last | .inter first last => refs first ++ refs last
  | .pair first last | .arrow first _ last _ => [first, last]
  | .record _ payload rest => payload :: refs rest
  | .recordDefault _ source fallback => refs source ++ [fallback]
  | .variant _ payload => [payload]
  | .mask _ source => refs source

def oldRefs (layer : RegularValueTypes.Layer Row Index) : List Index :=
  refs (CommonSyntax.ofOldLayer layer)

theorem refs_map (rename : Index → Target) (layer : CommonSyntax.Layer Row Index) :
    refs (layer.map rename) = (refs layer).map rename := by
  induction layer <;> simp_all [refs, CommonSyntax.Layer.map]

theorem oldRefs_map (rename : Index → Target) (layer : RegularValueTypes.Layer Row Index) :
    oldRefs (layer.map rename) = (oldRefs layer).map rename := by
  induction layer <;>
    simp_all [oldRefs, CommonSyntax.ofOldLayer, refs, RegularValueTypes.Layer.map]

/-- A finite block may use arbitrary numeric internal names, including
out-of-range references. Only its external states need existing support. -/
theorem finite_block {Index : Type u} {Layer : Type v}
    (next : Index → List Index) (references : Layer → List (Nat ⊕ Index))
    (empty : Layer) (emptyRefs : references empty = [])
    (body : List Layer) (block : Nat → Index)
    (unfolds : ∀ index, next (block index) =
      (references (body[index]?.getD empty)).map (Sum.elim block id))
    (external : ∀ layer ∈ body, ∀ state, .inr state ∈ references layer → FiniteAt next state)
    (root : Nat) : FiniteAt next (block root) := by
  let allRefs := body.flatMap references
  let internal := allRefs.filterMap (fun ref => match ref with | .inl n => some n | .inr _ => none)
  let leaves := allRefs.filterMap (fun ref => match ref with | .inl _ => none | .inr state => some state)
  let roots := (root :: internal).map block
  apply finite_extension next roots leaves ?_ ?_ (block root) (by simp [roots])
  · intro state member child childMember
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    rw [unfolds] at childMember
    cases found : body[index]? with
    | none => simp [found, emptyRefs] at childMember
    | some layer =>
      simp only [found, Option.getD_some] at childMember
      obtain ⟨ref, refMember, rfl⟩ := List.mem_map.mp childMember
      have included : ref ∈ allRefs := List.mem_flatMap.mpr
        ⟨layer, List.mem_of_getElem? found, refMember⟩
      cases ref with
      | inl index =>
        apply Or.inl
        apply List.mem_map.mpr
        refine ⟨index, List.mem_cons_of_mem _ ?_, rfl⟩
        exact List.mem_filterMap.mpr ⟨.inl index, included, rfl⟩
      | inr state =>
        exact Or.inr (List.mem_filterMap.mpr ⟨.inr state, included, rfl⟩)
  · intro state member
    obtain ⟨ref, included, equal⟩ := List.mem_filterMap.mp member
    cases ref with
    | inl index => cases equal
    | inr actual =>
      have same := Option.some.inj equal
      subst state
      obtain ⟨layer, layerMember, refMember⟩ := List.mem_flatMap.mp included
      exact external layer layerMember actual refMember

/-- Every concrete legacy state has a finite set closed under all guarded
references, even when its nested blocks contain cycles. -/
theorem old_finite_support (state : RegularInferenceModel.State Row) :
    FiniteAt (fun state => oldRefs (RegularInferenceModel.graph Row state)) state := by
  let next := fun state => oldRefs (RegularInferenceModel.graph Row state)
  let P := FiniteAt next
  change P state
  induction state using RegularInferenceModel.State.rec
    (motive_2 := fun layer => ∀ state ∈ oldRefs layer, P state)
    (motive_3 := fun body => ∀ layer ∈ body, ∀ ref ∈ oldRefs layer, Sum.elim (fun _ => True) P ref)
    (motive_4 := fun layer => ∀ ref ∈ oldRefs layer, Sum.elim (fun _ => True) P ref)
    (motive_5 := Sum.elim (fun _ => True) P) with
  | node layer supported =>
      apply finite_extension next [.node layer] (oldRefs layer) ?_ supported _ List.mem_cons_self
      intro state member child childMember
      have same : state = .node layer := by simpa using member
      subst state
      exact Or.inr childMember
  | block body root supported =>
      apply finite_block next oldRefs .bottom rfl body (RegularInferenceModel.State.block body) ?_ ?_ root
      · intro index
        exact oldRefs_map (RegularInferenceModel.rawBlockRef body) _
      · intro layer member state child
        exact supported layer member (.inr state) child
  | _ => simp_all [P, oldRefs, CommonSyntax.ofOldLayer, refs] <;> grind

/-- Every concrete Common state has finite closed support; this is derived
from its syntax, not supplied as a regularity premise on a witness. -/
theorem common_finite_support (state : CommonSyntax.State Row) :
    FiniteAt (fun state => refs (CommonSyntax.graph Row state)) state := by
  let next := fun state => refs (CommonSyntax.graph Row state)
  let P := FiniteAt next
  change P state
  induction state using CommonSyntax.State.rec
    (motive_2 := fun layer => ∀ state ∈ refs layer, P state)
    (motive_3 := fun body => ∀ layer ∈ body, ∀ ref ∈ refs layer, Sum.elim (fun _ => True) P ref)
    (motive_4 := fun layer => ∀ ref ∈ refs layer, Sum.elim (fun _ => True) P ref)
    (motive_5 := Sum.elim (fun _ => True) P) with
  | node layer supported =>
      apply finite_extension next [.node layer] (refs layer) ?_ supported _ List.mem_cons_self
      intro state member child childMember
      have same : state = .node layer := by simpa using member
      subst state
      exact Or.inr childMember
  | block body root supported =>
      apply finite_block next refs .bottom rfl body (CommonSyntax.State.block body) ?_ ?_ root
      · intro index
        exact refs_map (CommonSyntax.rawRef body) _
      · intro layer member state child
        exact supported layer member (.inr state) child
  | legacy state =>
      obtain ⟨states, member, closed⟩ := old_finite_support state
      refine ⟨states.map CommonSyntax.State.legacy, List.mem_map.mpr ⟨state, member, rfl⟩, ?_⟩
      intro state included child childMember
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp included
      change child ∈ refs ((CommonSyntax.ofOldLayer (RegularInferenceModel.graph Row old)).map
        CommonSyntax.State.legacy) at childMember
      rw [refs_map] at childMember
      obtain ⟨oldChild, oldChildMember, rfl⟩ := List.mem_map.mp childMember
      exact List.mem_map.mpr ⟨oldChild, closed old oldMember oldChild oldChildMember, rfl⟩
  | _ => simp_all [P, refs] <;> grind

/-- A finitely supported old graph has a representative in the actual old
regular carrier, with literally equal observations at every depth. -/
theorem old_representative {Index : Type u} {Row : Type v}
    (graph : RegularValueTypes.Graph Row Index) (root : Index)
    (supported : FiniteAt (fun state => oldRefs (graph state)) root) :
    ∃ type : RegularInferenceModel.Ty Row, ∀ depth,
      type.eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth) =
        (graph root).eval (RegularValueTypes.observe graph depth) := by
  classical
  obtain ⟨states, member, closed⟩ := supported
  let rootIndex : Fin states.length := ⟨states.idxOf root, List.idxOf_lt_length_of_mem member⟩
  let locate (state : Index) : Fin states.length :=
    if present : state ∈ states then ⟨states.idxOf state, List.idxOf_lt_length_of_mem present⟩ else rootIndex
  have located (state : Index) (present : state ∈ states) : states.get (locate state) = state := by
    simp only [locate, dite_eq_left present, List.get_eq_getElem]
    exact List.getElem_idxOf _
  have rootLocated : states.get rootIndex = root := List.getElem_idxOf _
  have mapCongr (layer : RegularValueTypes.Layer Row Index) (first last : Index → Index)
      (same : ∀ child ∈ oldRefs layer, first child = last child) : layer.map first = layer.map last := by
    induction layer <;>
      simp_all [oldRefs, refs, CommonSyntax.ofOldLayer, RegularValueTypes.Layer.map]
    all_goals grind
  let body : RegularValueTypes.FiniteGraph Row states.length :=
    fun index => (graph (states.get index)).map locate
  have morphism (index : Fin states.length) : (body index).map states.get = graph (states.get index) := by
    dsimp only [body]
    rw [RegularValueTypes.Layer.map_comp]
    calc
      _ = (graph (states.get index)).map id := mapCongr _ _ _
        (fun child childMember => located child (closed _ (List.get_mem _ index) child childMember))
      _ = _ := RegularValueTypes.Layer.map_id _
  let ref := RegularInferenceModel.finiteRef body
  refine ⟨RegularInferenceModel.graph Row (ref rootIndex), ?_⟩
  intro depth
  have concrete := RegularValueTypes.observe_morphism (graph := body)
    (RegularInferenceModel.graph Row) ref (RegularInferenceModel.finite_morphism body)
    (depth + 1) rootIndex
  have original := RegularValueTypes.observe_morphism (graph := body)
    graph states.get morphism (depth + 1) rootIndex
  rw [rootLocated] at original
  exact concrete.trans original.symm

end Yulang.CommonLegacyGraphSupport
