import Yulang.RegularValueTypes
import Yulang.ShadowRecordDemands

/-!
# Finite observations of regular values with hidden-field equality

The graph, layers, and observation function are exactly those of
`RegularValueTypes`. Only the finite comparison relation changes to the
decision-40 `ShadowSemanticRecords.Subtype`. Every finite observation therefore
obeys the adjacent shadow equation, including observations of arbitrary opaque
tails and cyclic payloads. Finite trees embed conservatively in this relation.

A layer's record tail is another finite layer, not a graph-state reference.
These results do not construct a coalescing for general open-tail constraint
graphs, decide regular subtyping, or add arbitrary-tail covariance.
-/

namespace Yulang.ShadowRegularValueTypes

open Inference
open RegularValueTypes (Layer Graph observe ofTree treeGraph treeBudget)

universe u v w

variable {Row : Type u} {State : Type v}

def At (graph : Graph Row State) (leRow : Row → Row → Prop) (depth : Nat)
    (left right : Layer Row State) : Prop :=
  ShadowSemanticRecords.Subtype leRow
    (left.eval (observe graph depth)) (right.eval (observe graph depth))

/-- Every observation uses the independent finite shadow relation. There is
no solver, successful traversal, or external depth bound in this definition. -/
def Subtype (graph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : Layer Row State) : Prop :=
  ∀ depth, At graph leRow depth left right

def NodeSubtype (graph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : State) : Prop :=
  Subtype graph leRow (graph left) (graph right)

def Equivalent (graph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : Layer Row State) : Prop :=
  Subtype graph leRow left right ∧ Subtype graph leRow right left

variable {graph : Graph Row State} {leRow : Row → Row → Prop}

theorem subtype_refl (type : Layer Row State) : Subtype graph leRow type type :=
  fun _ => .refl _

theorem subtype_trans {left middle right : Layer Row State}
    (first : Subtype graph leRow left middle) (last : Subtype graph leRow middle right) :
    Subtype graph leRow left right :=
  fun depth => .trans (first depth) (last depth)

theorem Equivalent.refl (type : Layer Row State) : Equivalent graph leRow type type :=
  ⟨subtype_refl _, subtype_refl _⟩

theorem Equivalent.symm {left right : Layer Row State}
    (same : Equivalent graph leRow left right) : Equivalent graph leRow right left :=
  ⟨same.2, same.1⟩

theorem Equivalent.trans {left middle right : Layer Row State}
    (first : Equivalent graph leRow left middle) (last : Equivalent graph leRow middle right) :
    Equivalent graph leRow left right :=
  ⟨subtype_trans first.1 last.1, subtype_trans last.2 first.2⟩

theorem old_subtype {left right : Layer Row State}
    (below : RegularValueTypes.Subtype graph leRow left right) :
    Subtype graph leRow left right :=
  fun depth => ShadowSemanticRecords.old_subtype (below depth)

/-- Existing guarded cyclic derivations remain sound. This does not assert
completeness of that historical proof system for the new relation. -/
theorem old_derivation_sound {left right : Layer Row State}
    (proof : RegularValueTypes.Derivation graph leRow [] [] left right) :
    Subtype graph leRow left right :=
  old_subtype proof.sound

theorem observe_subtype {left right : State}
    (below : NodeSubtype graph leRow left right) (depth : Nat) :
    ShadowSemanticRecords.Subtype leRow
      (observe graph depth left) (observe graph depth right) := by
  cases depth with
  | zero => exact .refl _
  | succ depth => exact below depth

theorem union_is_join (left right target : Layer Row State) :
    Subtype graph leRow (.union left right) target ↔
      Subtype graph leRow left target ∧ Subtype graph leRow right target := by
  constructor
  · intro below
    exact ⟨fun depth => (ShadowSemanticRecords.union_is_join _ _ _).mp (below depth) |>.1,
      fun depth => (ShadowSemanticRecords.union_is_join _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact .unionElim (first depth) (last depth)

theorem inter_is_meet (left right source : Layer Row State) :
    Subtype graph leRow source (.inter left right) ↔
      Subtype graph leRow source left ∧ Subtype graph leRow source right := by
  constructor
  · intro below
    exact ⟨fun depth => (ShadowSemanticRecords.inter_is_meet _ _ _).mp (below depth) |>.1,
      fun depth => (ShadowSemanticRecords.inter_is_meet _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact .interIntro (first depth) (last depth)

theorem pair_subtype {left left' right right' : State}
    (first : NodeSubtype graph leRow left left') (last : NodeSubtype graph leRow right right') :
    Subtype graph leRow (.pair left right) (.pair left' right') :=
  fun depth => .pair (observe_subtype first depth) (observe_subtype last depth)

theorem variant_subtype (label : Nat) {left right : State}
    (below : NodeSubtype graph leRow left right) :
    Subtype graph leRow (.variant label left) (.variant label right) :=
  fun depth => .variant (observe_subtype below depth)

theorem arrow_subtype {input input' output output' : State}
    {inputRow inputRow' outputRow outputRow' : Row}
    (before : NodeSubtype graph leRow input' input) (beforeRow : leRow inputRow' inputRow)
    (after : NodeSubtype graph leRow output output') (afterRow : leRow outputRow outputRow') :
    Subtype graph leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') :=
  fun depth => .arrow (observe_subtype before depth) beforeRow
    (observe_subtype after depth) afterRow

/-- Lookup of each proper record layer agrees with lookup after observation. -/
theorem eval_record_subtype (assignment : State → StructuralBase.Ty Row)
    {source target : Layer Row State}
    (sourceRecord : source.IsRecord) (targetRecord : target.IsRecord)
    (width : ∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual)
    (fields : ∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected →
      ShadowSemanticRecords.Subtype leRow (assignment actual) (assignment expected)) :
    ShadowSemanticRecords.Subtype leRow (source.eval assignment) (target.eval assignment) := by
  apply ShadowSemanticRecords.Subtype.record (Layer.eval_record assignment sourceRecord)
    (Layer.eval_record assignment targetRecord)
  · intro label value found
    rw [Layer.eval_lookup, Option.map_eq_some_iff] at found
    obtain ⟨expected, expectedFound, rfl⟩ := found
    obtain ⟨actual, actualFound⟩ := width label expected expectedFound
    exact ⟨assignment actual, by simp [Layer.eval_lookup, actualFound]⟩
  · intro label actual expected actualFound expectedFound
    rw [Layer.eval_lookup, Option.map_eq_some_iff] at actualFound expectedFound
    obtain ⟨a, aFound, rfl⟩ := actualFound
    obtain ⟨b, bFound, rfl⟩ := expectedFound
    exact fields label a b aFound bFound

theorem record_subtype {source target : Layer Row State}
    (sourceRecord : source.IsRecord) (targetRecord : target.IsRecord)
    (width : ∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual)
    (fields : ∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected → NodeSubtype graph leRow actual expected) :
    Subtype graph leRow source target :=
  fun depth => eval_record_subtype _ sourceRecord targetRecord width
    (fun label actual expected aFound bFound =>
      observe_subtype (fields label actual expected aFound bFound) depth)

/-- Semantic congruence includes both the visible payload and the entire tail. -/
theorem record_congr (label : Nat) {value value' : State} {rest rest' : Layer Row State}
    (head : Equivalent graph leRow (graph value) (graph value'))
    (tail : Equivalent graph leRow rest rest') :
    Equivalent graph leRow (.record label value rest) (.record label value' rest') :=
  ⟨fun depth => .recordCongr (observe_subtype head.1 depth) (observe_subtype head.2 depth)
      (tail.1 depth) (tail.2 depth),
    fun depth => .recordCongr (observe_subtype head.2 depth) (observe_subtype head.1 depth)
      (tail.2 depth) (tail.1 depth)⟩

/-- Only a syntactically proper demanded tail is used in this covariance rule. -/
theorem record_tail_covariant (label : Nat) (value : State) {rest rest' : Layer Row State}
    (rigid : rest'.IsRecord) (below : Subtype graph leRow rest rest') :
    Subtype graph leRow (.record label value rest) (.record label value rest') :=
  fun depth => .recordTail (Layer.eval_record _ rigid) (below depth)

theorem record_tail_semantically_rigid (label : Nat) (value : State)
    {rest rest' proper : Layer Row State} (rigid : proper.IsRecord)
    (same : Equivalent graph leRow rest' proper) (below : Subtype graph leRow rest rest') :
    Subtype graph leRow (.record label value rest) (.record label value rest') :=
  subtype_trans (record_tail_covariant label value rigid (subtype_trans below same.1))
    (record_congr label (.refl _) same.symm).1

theorem record_head (label : Nat) (value : State) {rest : Layer Row State}
    (admissible : Subtype graph leRow rest .emptyRecord) :
    Subtype graph leRow (.record label value rest) (.record label value .emptyRecord) :=
  record_tail_covariant label value .empty admissible

theorem record_width (label : Nat) (value : State) {rest : Layer Row State}
    (admissible : Subtype graph leRow rest .emptyRecord) :
    Subtype graph leRow (.record label value rest) .emptyRecord :=
  fun depth => ShadowSemanticRecords.record_width label _ (admissible depth)

/-- Empty and singleton demand elimination uses all observation depths; a
payload comparison is recovered one guarded edge below the outer record. -/
theorem record_empty_exact (label : Nat) (value : State) (rest : Layer Row State) :
    Subtype graph leRow (.record label value rest) .emptyRecord ↔
      Subtype graph leRow rest .emptyRecord := by
  constructor
  · intro below depth
    exact (ShadowRecordDemands.record_empty_exact label _ _).mp (below depth)
  · intro below depth
    exact (ShadowRecordDemands.record_empty_exact label _ _).mpr (below depth)

theorem record_singleton_same_exact (label : Nat) (value expected : State)
    (rest : Layer Row State) :
    Subtype graph leRow (.record label value rest) (.record label expected .emptyRecord) ↔
      NodeSubtype graph leRow value expected ∧ Subtype graph leRow rest .emptyRecord := by
  constructor
  · intro below
    exact ⟨fun depth =>
      ((ShadowRecordDemands.record_singleton_same_exact label _ _ _).mp (below (depth + 1))).1,
      fun depth => ((ShadowRecordDemands.record_singleton_same_exact label _ _ _).mp (below depth)).2⟩
  · rintro ⟨head, tail⟩ depth
    exact (ShadowRecordDemands.record_singleton_same_exact label _ _ _).mpr
      ⟨observe_subtype head depth, tail depth⟩

theorem record_singleton_other_exact (label demanded : Nat) (different : label ≠ demanded)
    (value expected : State) (rest : Layer Row State) :
    Subtype graph leRow (.record label value rest) (.record demanded expected .emptyRecord) ↔
      Subtype graph leRow rest (.record demanded expected .emptyRecord) := by
  constructor
  · intro below depth
    exact (ShadowRecordDemands.record_singleton_other_exact label demanded different _ _ _).mp
      (below depth)
  · intro below depth
    exact (ShadowRecordDemands.record_singleton_other_exact label demanded different _ _ _).mpr
      (below depth)

/-- The tail is any existing regular layer; no properness, admissibility,
acyclicity, finiteness of the graph, or row-algebra hypothesis is required. -/
theorem shadow_equivalent (label : Nat) (visible hidden : State) (rest : Layer Row State) :
    Equivalent graph leRow (.record label visible (.record label hidden rest))
      (.record label visible rest) :=
  ⟨fun _ => .shadowErase _ _ _ _, fun _ => .shadowInsert _ _ _ _⟩

theorem shadow_left_iff (label : Nat) (visible hidden : State)
    (rest target : Layer Row State) :
    Subtype graph leRow (.record label visible (.record label hidden rest)) target ↔
      Subtype graph leRow (.record label visible rest) target :=
  ⟨fun below => subtype_trans (shadow_equivalent label visible hidden rest).2 below,
    fun below => subtype_trans (shadow_equivalent label visible hidden rest).1 below⟩

theorem shadow_right_iff (label : Nat) (visible hidden : State)
    (rest source : Layer Row State) :
    Subtype graph leRow source (.record label visible (.record label hidden rest)) ↔
      Subtype graph leRow source (.record label visible rest) :=
  ⟨fun below => subtype_trans below (shadow_equivalent label visible hidden rest).1,
    fun below => subtype_trans below (shadow_equivalent label visible hidden rest).2⟩

theorem int_not_str : ¬ Subtype graph leRow (.base .int) (.base .str) :=
  fun below => ShadowSemanticRecords.int_not_str (below 0)

theorem top_not_bottom : ¬ Subtype graph leRow .top .bottom :=
  fun below => ShadowSemanticRecords.top_not_bottom (below 0)

/-! ## Exact preservation and reflection of graph embeddings -/

theorem subtype_morphism {Target : Type w}
    (target : Graph Row Target) (rename : State → Target)
    (commutes : ∀ state, (graph state).map rename = target (rename state))
    (left right : Layer Row State) :
    Subtype target leRow (left.map rename) (right.map rename) ↔
      Subtype graph leRow left right := by
  unfold Subtype At
  simp only [RegularValueTypes.eval_morphism target rename commutes]

theorem equivalent_morphism {Target : Type w}
    (target : Graph Row Target) (rename : State → Target)
    (commutes : ∀ state, (graph state).map rename = target (rename state))
    (left right : Layer Row State) :
    Equivalent target leRow (left.map rename) (right.map rename) ↔
      Equivalent graph leRow left right := by
  unfold Equivalent
  rw [subtype_morphism target rename commutes, subtype_morphism target rename commutes]

/-! ## Conservativity over finite shadow types -/

/-- Cutting guarded constructor references at any depth preserves every
finite shadow rule, including the entire arbitrary-tail equation. -/
theorem observe_tree_mono {left right : StructuralBase.Ty Row}
    (subtype : ShadowSemanticRecords.Subtype leRow left right) :
    ∀ depth, ShadowSemanticRecords.Subtype leRow
      (observe (treeGraph Row) depth left) (observe (treeGraph Row) depth right) := by
  induction subtype with
  | refl => exact fun _ => .refl _
  | trans _ _ first last => exact fun depth => .trans (first depth) (last depth)
  | bottom =>
      intro depth
      cases depth <;> exact .bottom _
  | top =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .top _
  | unionLeft =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .unionLeft _ _
  | unionRight =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .unionRight _ _
  | unionElim _ _ first last =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .unionElim (first (previous + 1)) (last (previous + 1))
  | interLeft =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .interLeft _ _
  | interRight =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .interRight _ _
  | interIntro _ _ first last =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .interIntro (first (previous + 1)) (last (previous + 1))
  | pair _ _ first last =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .pair (first previous) (last previous)
  | variant _ payload =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .variant (payload previous)
  | arrow _ inputRow _ outputRow input output =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .arrow (input previous) inputRow (output previous) outputRow
  | record sourceRecord targetRecord width _ fields =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous =>
          apply eval_record_subtype (observe (treeGraph Row) previous)
            (RegularValueTypes.ofTree_record sourceRecord)
            (RegularValueTypes.ofTree_record targetRecord)
          · simpa only [RegularValueTypes.ofTree_lookup] using width
          · intro label actual expected actualFound expectedFound
            exact fields label actual expected (by simpa using actualFound)
              (by simpa using expectedFound) previous
  | recordCongr _ _ _ _ headForward headBackward tailForward tailBackward =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous =>
          exact .recordCongr (headForward previous) (headBackward previous)
            (tailForward (previous + 1)) (tailBackward (previous + 1))
  | recordTail shape _ tail =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous =>
          exact .recordTail
            (Layer.eval_record _ (RegularValueTypes.ofTree_record shape))
            (tail (previous + 1))
  | shadowErase =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .shadowErase _ _ _ _
  | shadowInsert =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ => exact .shadowInsert _ _ _ _

/-- Regular observations introduce no extra comparisons between finite trees.
Reflection uses a computed sufficient tree budget, not a caller-supplied bound. -/
theorem finite_conservative (left right : StructuralBase.Ty Row) :
    Subtype (treeGraph Row) leRow (ofTree left) (ofTree right) ↔
      ShadowSemanticRecords.Subtype leRow left right := by
  constructor
  · intro proof
    have observed := proof (treeBudget left + treeBudget right)
    change ShadowSemanticRecords.Subtype leRow
      (observe (treeGraph Row) (treeBudget left + treeBudget right + 1) left)
      (observe (treeGraph Row) (treeBudget left + treeBudget right + 1) right) at observed
    rw [RegularValueTypes.observe_tree_exact left _ (by omega),
      RegularValueTypes.observe_tree_exact right _ (by omega)] at observed
    exact observed
  · intro proof depth
    exact observe_tree_mono proof (depth + 1)

end Yulang.ShadowRegularValueTypes
