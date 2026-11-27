import Yulang.GeneralDeclarativeI65I74CheckedPresentationMeaning474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph (Node Graph successors)
open CommonRoleGraphBisimulation (View observe ObservationallyEqual)

def recolorNode (convert : Nat → Nat) : Node n → Node n
  | .structural color children => .structural (convert color) children
  | other => other

def recolorGraph (g : Graph n) (convert : Nat → Nat) : Graph n := fun i => recolorNode convert (g i)

mutual
  def recolorView (convert : Nat → Nat) : View → View
    | .structural color children => .structural (convert color) (recolorViews convert children)
    | .nominal key children => .nominal key (recolorViews convert children)
    | other => other
  def recolorViews (convert : Nat → Nat) : List View → List View
    | [] => []
    | a::as => recolorView convert a :: recolorViews convert as
end

theorem recolor_list_is_pointwise (f : Nat → Nat) (vs : List View) :
    recolorViews f vs = vs.map (recolorView f) := by
  induction vs with
  | nil => rfl
  | cons a more ih => simp [recolorViews,ih]

theorem recoloring_never_changes_any_actual_successors (g : Graph n) (f : Nat → Nat) :
    successors (recolorGraph g f) = successors g := by
  funext i
  cases atSite : g i <;> simp [successors,recolorGraph,recolorNode,atSite]

theorem recoloring_observations_is_only_signature_renaming (g : Graph n) (f : Nat → Nat) :
    ∀ d i, observe (recolorGraph g f) d i = recolorView f (observe g d i) := by
  intro depth
  induction depth with
  | zero => intro; rfl
  | succ d ih =>
    intro i
    cases node : g i <;> simp only [observe,recolorGraph,recolorNode,recolorView,node,
      recolor_list_is_pointwise,List.map_map]
    all_goals first
      | rfl
      | congr 1; apply List.map_congr_left; intro x _; exact ih x

mutual
  theorem recolor_then_recover (f back : Nat → Nat) (inverse : ∀ a, back (f a) = a) (v : View) :
      recolorView back (recolorView f v) = v := by
    cases v <;> simp [recolorView,inverse,recolors_then_recover f back inverse]
  theorem recolors_then_recover (f back : Nat → Nat) (inverse : ∀ a, back (f a) = a)
      (v : List View) : recolorViews back (recolorViews f v) = v := by
    cases v <;> simp [recolorViews,recolor_then_recover f back inverse,recolors_then_recover f back inverse]
end

theorem injective_recoloring_preserves_exact_observation_equivalence
    (g : Graph n) (f : Nat → Nat) (injective : ∀ a b, f a = f b → a = b) (i j : Fin n) :
    ObservationallyEqual (recolorGraph g f) i j ↔ ObservationallyEqual g i j := by
  classical
  let back (y : Nat) := if h : ∃ x, f x = y then Classical.choose h else 0
  have inv (a : Nat) : back (f a) = a := by
    unfold back
    rw [dite_eq_left (show ∃ x, f x = f a from ⟨a,rfl⟩)]
    exact injective _ _ (Classical.choose_spec (show ∃ x, f x = f a from ⟨a,rfl⟩))
  constructor
  · intro same d
    have images := same d
    rw [recoloring_observations_is_only_signature_renaming,recoloring_observations_is_only_signature_renaming] at images
    have value := congrArg (recolorView back) images
    simpa only [recolor_then_recover f back inv] using value
  · intro same d
    rw [recoloring_observations_is_only_signature_renaming,recoloring_observations_is_only_signature_renaming,same d]

theorem injective_recoloring_preserves_actual_nonempty_returns
    (g : Graph n) (f : Nat → Nat) (injective : ∀ a b, f a = f b → a = b) (i : Fin n) :
    ReturnsUpToEquality (recolorGraph g f) i ↔ ReturnsUpToEquality g i := by
  unfold ReturnsUpToEquality
  simp only [recoloring_never_changes_any_actual_successors,
    injective_recoloring_preserves_exact_observation_equivalence g f injective]

end Yulang.QuotientObservation471

namespace Yulang.QuotientObservation471
open CommonRoleRegularGraph (Node Graph)
open GeneralNormalizedObservation (Shape)

def commonPalette (a b : List Shape) : List Shape := (a ++ b).eraseDups

theorem old_palettes_embed_in_shared_palette (a b : List Shape) :
    (a ⊆ commonPalette a b) ∧ (b ⊆ commonPalette a b) := by
  constructor <;> intro sig shown
  · simpa [commonPalette] using (Or.inl shown : sig ∈ a ∨ sig ∈ b)
  · simpa [commonPalette] using (Or.inr shown : sig ∈ a ∨ sig ∈ b)

def mappedIndex (prior into : List Shape) (i : Nat) : Nat :=
  match prior[i]? with
  | some shape => into.idxOf shape
  | none => into.length + i

theorem stored_palette_index_finds_exact_shape (prior : List Shape) (shape : Shape)
    (present : shape ∈ prior) : prior[prior.idxOf shape]? = some shape := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem present),List.getElem_idxOf]

theorem common_palette_renumbering_is_injective
    {prior into : List Shape} (unique : prior.Nodup) (all : prior ⊆ into) :
    ∀ i j, mappedIndex prior into i = mappedIndex prior into j → i = j := by
  intro i j same
  unfold mappedIndex at same
  cases a : prior[i]? with
  | none =>
    cases b : prior[j]? with
    | none => simp only [a,b] at same; omega
    | some shape =>
      have known := List.idxOf_lt_length_of_mem (all (List.mem_of_getElem? b))
      simp only [a,b] at same
      omega
  | some shape =>
    cases b : prior[j]? with
    | none =>
      have known := List.idxOf_lt_length_of_mem (all (List.mem_of_getElem? a))
      simp only [a,b] at same
      omega
    | some other =>
      simp only [a,b] at same
      have left := stored_palette_index_finds_exact_shape into _ (all (List.mem_of_getElem? a))
      have right := stored_palette_index_finds_exact_shape into _ (all (List.mem_of_getElem? b))
      rw [←same] at right
      have identical := Option.some.inj (left.symm.trans right)
      subst other
      obtain ⟨hi,equal⟩ := List.getElem?_eq_some_iff.mp a
      obtain ⟨hj,also⟩ := List.getElem?_eq_some_iff.mp b
      exact unique.getElem_inj.mp (equal.trans also.symm)

end Yulang.QuotientObservation471

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open GeneralNormalizedObservation (Shape)
open G04FiniteConstructorSemantics473 (Shell)
open ObservationSyntax471 (codeLabel)
open QuotientObservation471 (mappedIndex stored_palette_index_finds_exact_shape recolorNode)
open CommonRoleRegularGraph (Node)

theorem same_typed_shell_in_larger_palette_only_renumbers_its_structural_code
    {prior into : List Shape} {shell : Shell (Fin n)} {node : Node n}
    (all : prior ⊆ into) (actual : encodeShell prior shell = some node) :
    encodeShell into shell = some (recolorNode (mappedIndex prior into) node) := by
  unfold encodeShell at actual ⊢
  cases label : shellHead shell with
  | scalar b =>
    have form := Option.some.inj (show some (.scalar (CommonRoleScalarSourceInspection.code b)) = some node
      from by simpa [label,codeLabel] using actual)
    subst node
    simp [codeLabel,recolorNode]
  | nominal tag =>
    have form := Option.some.inj (show some (.nominal tag (shellChildren shell)) = some node
      from by simpa [label,codeLabel] using actual)
    subst node
    simp [codeLabel,recolorNode]
  | structural shape =>
    by_cases previous : shape ∈ prior
    · have form := Option.some.inj (show some (.structural (prior.idxOf shape) (shellChildren shell)) = some node
        from by simpa [label,codeLabel,previous] using actual)
      subst node
      simp [codeLabel,all previous,recolorNode,mappedIndex,stored_palette_index_finds_exact_shape _ _ previous]
    · simp [label,codeLabel,previous] at actual

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65 (Model)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleGraphBisimulation (Relation)
open QuotientObservation471 (ConeWire Wire embedded cone cone_replay_sound
  checkAcrossWitness commonPalette mappedIndex recolorGraph old_palettes_embed_in_shared_palette
  common_palette_renumbering_is_injective injective_recoloring_preserves_actual_nonempty_returns
  finite_relation_witness_preserves_the_regular_observation
  quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

theorem exact_checked_presentations_can_use_separately_ordered_constructor_palettes
    {p : FullProblem} {a : Positions n} {b : Positions m}
    {left : Relation n} {right : Relation m} {i : Fin n} {j : Fin m}
    {wl : ConeWire n u} {wr : ConeWire m v} {pl : Wire u k} {pr : Wire v l}
    {sl sr : Bool} {relation : Relation (u+v)}
    (readL : readAlternatives p.old.state.core a left i wl pl = some sl)
    (readR : readAlternatives p.old.state.core b right j wr pr = some sr)
    (comparison : checkAcrossWitness
      (recolorGraph (cone wl) (mappedIndex a.signs (commonPalette a.signs b.signs)))
      (recolorGraph (cone wr) (mappedIndex b.signs (commonPalette a.signs b.signs)))
      wl.site wr.site relation = true) :
    sl = sr ∧
    (∀ m : Model, FitsFull p.state m →
      Equivalent (interpretedAt p.old.state.core a m.assignment i)
        (interpretedAt p.old.state.core b m.assignment j)) := by
  let new := commonPalette a.signs b.signs
  obtain ⟨incL,incR⟩ := old_palettes_embed_in_shared_palette a.signs b.signs
  have uniqL := (LiteralVisits473.accepted_observation_yields_all_input_guards readL).1
  have uniqR := (LiteralVisits473.accepted_observation_yields_all_input_guards readR).1
  have leftOne := common_palette_renumbering_is_injective uniqL incL
  have rightOne := common_palette_renumbering_is_injective uniqR incR
  have l := accepted_alternative_graph_is_actual_cone_replay readL
  have r := accepted_alternative_graph_is_actual_cone_replay readR
  have exactL := (cone_replay_sound l).1
  have exactR := (cone_replay_sound r).1
  have known := finite_relation_witness_preserves_the_regular_observation comparison
  have signL := ((cone_replay_sound l).2).trans (QuotientObservation471.cone_cycle_iff_ambient_at_the_actual_site exactL).symm
  have signR := ((cone_replay_sound r).2).trans (QuotientObservation471.cone_cycle_iff_ambient_at_the_actual_site exactR).symm
  have changedL := injective_recoloring_preserves_actual_nonempty_returns (cone wl) (mappedIndex a.signs new) leftOne wl.site
  have changedR := injective_recoloring_preserves_actual_nonempty_returns (cone wr) (mappedIndex b.signs new) rightOne wr.site
  have related := quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation known
  have bits : sl = true ↔ sr = true :=
    signL.trans (changedL.symm.trans (related.trans (changedR.trans signR.symm)))
  have same : sl = sr := by
    cases sl <;> cases sr <;> simp_all
  refine ⟨same,?_⟩
  let ta : ∀ i, TypedObservationAt p.old.state.core a (embedded wl) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactL i)
  let tb : ∀ i, TypedObservationAt p.old.state.core b (embedded wr) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactR i)
  have ca : ∀ i, encodeShell new (typedBy ta i) = some (recolorGraph (cone wl) (mappedIndex a.signs new) i) := by
    intro k
    exact same_typed_shell_in_larger_palette_only_renumbers_its_structural_code incL
      (Classical.choose_spec (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactL k))
  have cb : ∀ j, encodeShell new (typedBy tb j) = some (recolorGraph (cone wr) (mappedIndex b.signs new) j) := by
    intro k
    exact same_typed_shell_in_larger_palette_only_renumbers_its_structural_code incR
      (Classical.choose_spec (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site exactR k))
  have equalType := equivalent_typed_value_of_checked_regular_presentations_over_one_signature ca cb known
  intro m fit
  have aFit := same_fits_full_input_keeps_unchanged_typed_observation_graph ta m fit wl.site
  have bFit := same_fits_full_input_keeps_unchanged_typed_observation_graph tb m fit wr.site
  rw [exactL.1] at aFit
  rw [exactR.1] at bFit
  exact eqv_trans aFit (eqv_trans equalType (eqv_symm bFit))

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
