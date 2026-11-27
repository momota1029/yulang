import Yulang.GeneralDeclarativeI65I74TypedConeReadback474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open CommonRoleRegularGraph (Graph Node)
open CommonRoleGraphBisimulation (View observe ObservationallyEqual)
open G04FiniteConstructorSemantics473 (Shell FT body shellLayer rowLayer)
open CommonNominalFullCarrier (Row Ty Equivalent observeTy)
open CommonNominalSyntax (Layer)

def scalarForCode : Nat → FT
  | 0 => .base .int
  | 1 => .base .str
  | 2 => .base .bool
  | 3 => .base .unit
  | _ => .bottom

theorem scalar_decode_is_actual (k : Inference.Base) :
    scalarForCode (CommonRoleScalarSourceInspection.code k) = .base k := by
  cases k <;> rfl

def decodeRowShape : List Nat → List FT → FT
  | k::ks,a::args => .record k a (decodeRowShape ks args)
  | [],[] => .emptyRecord
  | _,_ => .bottom

def decodeStructuralShape : GeneralNormalizedObservation.Shape → List FT → FT
  | .pair,[a,b] => .pair a b
  | .record labels,children => decodeRowShape labels children
  | .exactEmpty,[] => .exactEmpty
  | .variant k,[a] => .variant k a
  | _,_ => .bottom

mutual
  def readRegularView (signs : List GeneralNormalizedObservation.Shape) : View → FT
    | .cut | .unresolved => .bottom
    | .scalar name => scalarForCode name
    | .structural ix views =>
      match signs[ix]? with
      | none => .bottom
      | some shape => decodeStructuralShape shape (readRegularViews signs views)
    | .nominal name args => .nominal name ((readRegularViews signs args).map Sum.inl)
  def readRegularViews (signs : List GeneralNormalizedObservation.Shape) : List View → List FT
    | [] => []
    | a::as => readRegularView signs a :: readRegularViews signs as
end

theorem reads_regular_views_as_map (signs : List GeneralNormalizedObservation.Shape)
    (xs : List View) : readRegularViews signs xs = xs.map (readRegularView signs) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [readRegularViews,ih]

theorem decode_row_shape_has_original_order_and_exact_operands
    (d : Nat) (meaning : α → FT) (fields : List (Nat × α)) :
    decodeRowShape (fields.map Prod.fst) (fields.map (meaning ∘ Prod.snd)) =
      (rowLayer fields).evalAt d meaning := by
  induction fields with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨tag,a⟩ := x
    simp only [List.map_cons,decodeRowShape,rowLayer,Layer.evalAt,Function.comp_def]
    exact congrArg (CommonNominalFinite.Ty.record tag (meaning a)) ih

def closedShellGraph (g : Fin n → Shell (Fin n)) : CommonNominalSyntax.Graph Row (Fin n) :=
  fun i => shellLayer (g i)

theorem typed_block_graph_embeds_exactly (g : Fin n → Shell (Fin n)) (d : Nat) (i : Fin n) :
    CommonNominalSyntax.observe (closedShellGraph g) d i =
      CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) d (CommonNominalSyntax.closeBlock (body g) i) := by
  symm
  apply CommonNominalSyntax.observe_morphism
  intro i
  simp [closedShellGraph,body,CommonNominalSyntax.blockRef,Function.comp_def]

open ObservationSyntax471 (codeLabel)

theorem constructor_observation_decodes_to_the_finite_typed_block_approximation
    {sigs : List GeneralNormalizedObservation.Shape} {numeric : Graph n}
    {typed : Fin n → Shell (Fin n)}
    (exact : ∀ i, encodeShell sigs (typed i) = some (numeric i)) :
    ∀ d i, readRegularView sigs (observe numeric d i) =
      CommonNominalSyntax.observe (closedShellGraph typed) d i := by
  intro d
  induction d with
  | zero => intro; rfl
  | succ d ih =>
    intro i
    have read := exact i
    cases kind : typed i with
    | scalar k =>
      have node : numeric i = .scalar (CommonRoleScalarSourceInspection.code k) := by
        simpa [encodeShell,kind,codeLabel,shellHead] using read.symm
      simp [observe,node,readRegularView,scalar_decode_is_actual,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer,Layer.evalAt]
    | unaryNominal name x =>
      have node : numeric i = .nominal name [x] := by
        simpa [encodeShell,kind,codeLabel,shellHead,shellChildren] using read.symm
      simp [observe,node,readRegularView,readRegularViews,ih,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer,Layer.evalAt]
    | pair a b =>
      have has : GeneralNormalizedObservation.Shape.pair ∈ sigs := by
        by_cases yes : GeneralNormalizedObservation.Shape.pair ∈ sigs
        · exact yes
        · simp [encodeShell,kind,codeLabel,shellHead,yes] at read
      have node : numeric i = .structural (sigs.idxOf .pair) [a,b] := by
        simpa [encodeShell,kind,codeLabel,shellHead,shellChildren,has] using read.symm
      have sign : sigs[sigs.idxOf .pair]? = some .pair := by
        rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem has),List.getElem_idxOf]
      simp [observe,node,readRegularView,readRegularViews,ih,sign,decodeStructuralShape,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer,Layer.evalAt]
    | variant tag x =>
      have has : GeneralNormalizedObservation.Shape.variant tag ∈ sigs := by
        by_cases yes : GeneralNormalizedObservation.Shape.variant tag ∈ sigs
        · exact yes
        · simp [encodeShell,kind,codeLabel,shellHead,yes] at read
      have node : numeric i = .structural (sigs.idxOf (.variant tag)) [x] := by
        simpa [encodeShell,kind,codeLabel,shellHead,shellChildren,has] using read.symm
      have sign : sigs[sigs.idxOf (.variant tag)]? = some (.variant tag) := by
        rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem has),List.getElem_idxOf]
      simp [observe,node,readRegularView,readRegularViews,ih,sign,decodeStructuralShape,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer,Layer.evalAt]
    | exactEmpty =>
      have has : GeneralNormalizedObservation.Shape.exactEmpty ∈ sigs := by
        by_cases yes : GeneralNormalizedObservation.Shape.exactEmpty ∈ sigs
        · exact yes
        · simp [encodeShell,kind,codeLabel,shellHead,yes] at read
      have node : numeric i = .structural (sigs.idxOf .exactEmpty) [] := by
        simpa [encodeShell,kind,codeLabel,shellHead,shellChildren,has] using read.symm
      have sign : sigs[sigs.idxOf .exactEmpty]? = some .exactEmpty := by
        rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem has),List.getElem_idxOf]
      simp [observe,node,readRegularView,readRegularViews,sign,decodeStructuralShape,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer,Layer.evalAt]
    | row fields =>
      have has : GeneralNormalizedObservation.Shape.record (fields.map Prod.fst) ∈ sigs := by
        by_cases yes : GeneralNormalizedObservation.Shape.record (fields.map Prod.fst) ∈ sigs
        · exact yes
        · simp [encodeShell,kind,codeLabel,shellHead,yes] at read
      have node : numeric i = .structural (sigs.idxOf (.record (fields.map Prod.fst))) (fields.map Prod.snd) := by
        simpa [encodeShell,kind,codeLabel,shellHead,shellChildren,has] using read.symm
      have sign : sigs[sigs.idxOf (.record (fields.map Prod.fst))]? = some (.record (fields.map Prod.fst)) := by
        rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem has),List.getElem_idxOf]
      simp only [observe,node,readRegularView,sign,decodeStructuralShape,reads_regular_views_as_map,List.map_map,
        CommonNominalSyntax.observe,closedShellGraph,kind,shellLayer]
      rw [show List.map (readRegularView sigs ∘ observe numeric d ∘ Prod.snd) fields =
        List.map (CommonNominalSyntax.observe (closedShellGraph typed) d ∘ Prod.snd) fields by
          apply List.map_congr_left
          intro x _
          exact ih x.2]
      exact decode_row_shape_has_original_order_and_exact_operands _ _ _

theorem exact_observational_equivalence_implies_equal_typed_regular_values
    {sigs : List GeneralNormalizedObservation.Shape} {numeric : Graph n}
    {typed : Fin n → Shell (Fin n)}
    (exact : ∀ i, encodeShell sigs (typed i) = some (numeric i))
    {left right : Fin n} (same : ObservationallyEqual numeric left right) :
    Equivalent (G04FiniteConstructorSemantics473.value typed left)
      (G04FiniteConstructorSemantics473.value typed right) := by
  have sameMeaning (d : Nat) : observeTy d (G04FiniteConstructorSemantics473.value typed left) =
      observeTy d (G04FiniteConstructorSemantics473.value typed right) := by
    change CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (d+1)
        (CommonNominalSyntax.closeBlock (body typed) left) =
      CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (d+1)
        (CommonNominalSyntax.closeBlock (body typed) right)
    rw [←typed_block_graph_embeds_exactly,←typed_block_graph_embeds_exactly,
      ←constructor_observation_decodes_to_the_finite_typed_block_approximation exact,
      ←constructor_observation_decodes_to_the_finite_typed_block_approximation exact,
      same (d+1)]
  constructor <;> intro d <;> rw [sameMeaning d] <;> exact CommonNominalFullDemand.producerLe_refl _

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65 (Model)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open QuotientObservation471 (ConeWire Wire ExactCone ExactPartition embedded cone classOf replayCone
  cone_replay_sound safe_replay_exact positive_replay_exact exact_classes_are_regular_observation_equality)

theorem equal_classes_of_an_actually_checked_observation_have_equal_type_value_in_every_original_fit
    {p : FullProblem} {t : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n k} {partition : Wire k l} {bit}
    (read : readAlternatives p.old.state.core t rel root scope partition = some bit)
    {left right : Fin k} (sameClass : classOf partition left = classOf partition right)
    (m : Model) (fit : FitsFull p.state m) :
    Equivalent (interpretedAt p.old.state.core t m.assignment (embedded scope left))
      (interpretedAt p.old.state.core t m.assignment (embedded scope right)) := by
  have computed : replayCone (graphOf p.old.state.core t) root scope partition = some bit := by
    unfold readAlternatives at read
    split at read
    · exact read
    · cases read
  have complete := (cone_replay_sound computed).1
  have validates : ExactPartition (cone scope) partition := by
    unfold replayCone at computed
    split at computed
    · cases bit
      · exact (safe_replay_exact.mp computed).1
      · exact (positive_replay_exact.mp computed).1
    · cases computed
  let fitted : ∀ i, TypedObservationAt p.old.state.core t (embedded scope) i :=
    fun i => Classical.choose (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site complete i)
  have coding : ∀ i, encodeShell t.signs (typedBy fitted i) = some (cone scope i) :=
    fun i => Classical.choose_spec (exact_closed_observation_supplies_a_typed_shell_at_each_actual_site complete i)
  have closedType := same_fits_full_input_keeps_unchanged_typed_observation_graph fitted m fit
  have sameView := (exact_classes_are_regular_observation_equality validates left right).mp sameClass
  have compare := exact_observational_equivalence_implies_equal_typed_regular_values coding sameView
  exact eqv_trans (closedType left) (eqv_trans compare (eqv_symm (closedType right)))

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65 (Model)
open CommonNominalFullCarrier (Equivalent)
open QuotientObservation471 (ConeWire Wire ExactCone ExactPartition embedded cone classOf replayCone
  cone_replay_sound safe_replay_exact positive_replay_exact exact_classes_are_regular_observation_equality
  quotient_cycle_iff_returns_up_to_equality)
open CommonRoleRegularGraph (successors)
open FiniteWorklist (Path)

theorem actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit
    {p : FullProblem} {t : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n k} {partition : Wire k l}
    (read : readAlternatives p.old.state.core t rel root scope partition = some true) :
    ∃ first last : Fin k,
      first ∈ successors (cone scope) scope.site ∧
      Path (successors (cone scope)) first last ∧
      classOf partition last = classOf partition scope.site ∧
      (∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core t m.assignment (embedded scope last))
          (interpretedAt p.old.state.core t m.assignment (embedded scope scope.site))) := by
  have computed : replayCone (graphOf p.old.state.core t) root scope partition = some true := by
    unfold readAlternatives at read
    split at read
    · exact read
    · cases read
  unfold replayCone at computed
  split at computed
  · obtain ⟨checked,cycle⟩ := positive_replay_exact.mp computed
    obtain ⟨first,actual,last,rest,sameView⟩ :=
      (quotient_cycle_iff_returns_up_to_equality checked scope.site).mp cycle
    have same := (exact_classes_are_regular_observation_equality checked last scope.site).mpr sameView
    exact ⟨first,last,actual,rest,same,fun m fit =>
      equal_classes_of_an_actually_checked_observation_have_equal_type_value_in_every_original_fit
        read same m fit⟩
  · cases computed

theorem actual_safe_quotient_never_returns_to_its_own_observation_class
    {p : FullProblem} {t : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n k} {partition : Wire k l}
    (read : readAlternatives p.old.state.core t rel root scope partition = some false) :
      ∀ first ∈ successors (cone scope) scope.site, ∀ last,
        Path (successors (cone scope)) first last →
        classOf partition last ≠ classOf partition scope.site := by
  have computed : replayCone (graphOf p.old.state.core t) root scope partition = some false := by
    unfold readAlternatives at read
    split at read
    · exact read
    · cases read
  unfold replayCone at computed
  split at computed
  · obtain ⟨checked,safe⟩ := safe_replay_exact.mp computed
    intro first adjacent last tail same
    have exact := (exact_classes_are_regular_observation_equality checked last scope.site).mp same
    exact safe ((quotient_cycle_iff_returns_up_to_equality checked scope.site).mpr
      ⟨first,adjacent,last,tail,exact⟩)
  · cases computed

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
