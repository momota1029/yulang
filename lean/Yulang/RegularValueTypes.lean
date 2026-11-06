import Yulang.StructuralBase

/-!
# An independent guarded model for recursive value types

A graph describes one finite lattice layer at each state. Recursive references
occur below a value constructor; record spines remain finite and retain the
existing first-field-wins lookup. The graph need not be acyclic. `Fin n` gives
the finite graphs needed by a regular-type implementation.

Subtyping is defined by all finite structural observations, using the existing
independent `StructuralBase.Subtype`. It is not defined by a constraint solver,
by a successful graph traversal, or by the least solution of an effect row.
The definition preserves the existing finite, non-distributive value algebra.

The declarative proof system below has separate usable and delayed hypotheses.
An assumed comparison becomes usable only after crossing a value constructor.
Its soundness theorem accounts for arbitrary cycles, lattice rules, and cuts;
in particular a naked cyclic assumption cannot prove `any <= never`.

This module supplies a recursive subtype foundation, not the theorem that an
arbitrary saturated bound graph has an exact principal coalescing.
-/

namespace Yulang.RegularValueTypes

open Inference

universe u v

/-- One finite outer layer. References are guarded by constructors. -/
inductive Layer (Row : Type u) (State : Type v) where
  | base : Base → Layer Row State
  | bottom : Layer Row State
  | top : Layer Row State
  | union : Layer Row State → Layer Row State → Layer Row State
  | inter : Layer Row State → Layer Row State → Layer Row State
  | pair : State → State → Layer Row State
  | emptyRecord : Layer Row State
  | record : Nat → State → Layer Row State → Layer Row State
  | variant : Nat → State → Layer Row State
  | arrow : State → Row → State → Row → Layer Row State

abbrev Graph (Row : Type u) (State : Type v) := State → Layer Row State

abbrev FiniteGraph (Row : Type u) (size : Nat) := Graph Row (Fin size)

namespace Layer

variable {Row : Type u} {State : Type v}

def eval (assignment : State → StructuralBase.Ty Row) :
    Layer Row State → StructuralBase.Ty Row
  | .base value => .base value
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (eval assignment left) (eval assignment right)
  | .inter left right => .inter (eval assignment left) (eval assignment right)
  | .pair left right => .pair (assignment left) (assignment right)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (assignment value) (eval assignment rest)
  | .variant label value => .variant label (assignment value)
  | .arrow input inputRow output outputRow =>
      .arrow (assignment input) inputRow (assignment output) outputRow

def lookup (label : Nat) : Layer Row State → Option State
  | .record name value rest => if label = name then some value else lookup label rest
  | _ => none

inductive IsRecord : Layer Row State → Prop where
  | empty : IsRecord .emptyRecord
  | field : IsRecord rest → IsRecord (.record label value rest)

@[simp] theorem eval_lookup (assignment : State → StructuralBase.Ty Row)
    (type : Layer Row State) (label : Nat) :
    (eval assignment type).lookup label = (lookup label type).map assignment := by
  induction type with
  | record name value rest ih =>
      by_cases equal : label = name <;> simp [eval, lookup, equal, ih]
  | _ => rfl

theorem eval_record (assignment : State → StructuralBase.Ty Row)
    {type : Layer Row State} (shape : IsRecord type) :
    StructuralBase.IsRecord (eval assignment type) := by
  induction shape with
  | empty => exact .empty
  | field _ ih => exact .field ih

/-- Rename graph references without changing any row or constructor. -/
def map {Target : Type w} (rename : State → Target) : Layer Row State → Layer Row Target
  | .base value => .base value
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (map rename left) (map rename right)
  | .inter left right => .inter (map rename left) (map rename right)
  | .pair left right => .pair (rename left) (rename right)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (rename value) (map rename rest)
  | .variant label value => .variant label (rename value)
  | .arrow input inputRow output outputRow =>
      .arrow (rename input) inputRow (rename output) outputRow

@[simp] theorem eval_map {Target : Type w} (rename : State → Target)
    (assignment : Target → StructuralBase.Ty Row) (type : Layer Row State) :
    (type.map rename).eval assignment = type.eval (fun state => assignment (rename state)) := by
  induction type <;> simp [map, eval, *]

@[simp] theorem map_id (type : Layer Row State) : type.map id = type := by
  induction type <;> simp [map, *]

@[simp] theorem map_comp {Middle : Type w} {Target : Type z}
    (first : State → Middle) (second : Middle → Target) (type : Layer Row State) :
    (type.map first).map second = type.map (fun state => second (first state)) := by
  induction type <;> simp [map, *]

end Layer

variable {Row : Type u} {State : Type v}

/-- Observe at most `depth` recursive constructor edges. No search is involved. -/
def observe (graph : Graph Row State) : Nat → State → StructuralBase.Ty Row
  | 0, _ => .bottom
  | depth + 1, state => Layer.eval (observe graph depth) (graph state)

/-- A finite observation of a comparison of two graph-rooted layers. -/
def At (graph : Graph Row State) (leRow : Row → Row → Prop) (depth : Nat)
    (left right : Layer Row State) : Prop :=
  StructuralBase.Subtype leRow
    (left.eval (observe graph depth)) (right.eval (observe graph depth))

/-- Independent recursive subtyping: every finite observation is a subtype. -/
def Subtype (graph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : Layer Row State) : Prop :=
  ∀ depth, At graph leRow depth left right

/-- A state denotes its defining layer, including any recursive back edges. -/
def NodeSubtype (graph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : State) : Prop :=
  Subtype graph leRow (graph left) (graph right)

variable {graph : Graph Row State} {leRow : Row → Row → Prop}

theorem subtype_refl (type : Layer Row State) : Subtype graph leRow type type :=
  fun _ => .refl _

theorem subtype_trans {a b c : Layer Row State}
    (left : Subtype graph leRow a b) (right : Subtype graph leRow b c) :
    Subtype graph leRow a c :=
  fun depth => .trans (left depth) (right depth)

theorem node_subtype_refl (state : State) : NodeSubtype graph leRow state state :=
  subtype_refl _

theorem node_subtype_trans {a b c : State}
    (left : NodeSubtype graph leRow a b) (right : NodeSubtype graph leRow b c) :
    NodeSubtype graph leRow a c :=
  subtype_trans left right

abbrev Context (Row : Type u) (State : Type v) :=
  List (Layer Row State × Layer Row State)

/-- Hypotheses may be reused only in the usable context. Constructors unlock
the delayed context for their recursive premises. Lattice rules do not. -/
inductive Derivation (graph : Graph Row State) (leRow : Row → Row → Prop) :
    Context Row State → Context Row State → Layer Row State → Layer Row State → Prop where
  | hyp : (a, b) ∈ usable → Derivation graph leRow usable delayed a b
  | assume : Derivation graph leRow usable ((a, b) :: delayed) a b →
      Derivation graph leRow usable delayed a b
  | refl : Derivation graph leRow usable delayed a a
  | trans : Derivation graph leRow usable delayed a b →
      Derivation graph leRow usable delayed b c → Derivation graph leRow usable delayed a c
  | bottom : Derivation graph leRow usable delayed .bottom a
  | top : Derivation graph leRow usable delayed a .top
  | unionLeft : Derivation graph leRow usable delayed a (.union a b)
  | unionRight : Derivation graph leRow usable delayed b (.union a b)
  | unionElim : Derivation graph leRow usable delayed a c →
      Derivation graph leRow usable delayed b c →
      Derivation graph leRow usable delayed (.union a b) c
  | interLeft : Derivation graph leRow usable delayed (.inter a b) a
  | interRight : Derivation graph leRow usable delayed (.inter a b) b
  | interIntro : Derivation graph leRow usable delayed c a →
      Derivation graph leRow usable delayed c b →
      Derivation graph leRow usable delayed c (.inter a b)
  | pair : Derivation graph leRow (usable ++ delayed) [] (graph a) (graph a') →
      Derivation graph leRow (usable ++ delayed) [] (graph b) (graph b') →
      Derivation graph leRow usable delayed (.pair a b) (.pair a' b')
  | variant : Derivation graph leRow (usable ++ delayed) [] (graph a) (graph b) →
      Derivation graph leRow usable delayed (.variant label a) (.variant label b)
  | arrow : Derivation graph leRow (usable ++ delayed) [] (graph input') (graph input) →
      leRow inputRow' inputRow →
      Derivation graph leRow (usable ++ delayed) [] (graph output) (graph output') →
      leRow outputRow outputRow' →
      Derivation graph leRow usable delayed
        (.arrow input inputRow output outputRow) (.arrow input' inputRow' output' outputRow')
  | record : Layer.IsRecord source → Layer.IsRecord target →
      (∀ label expected, target.lookup label = some expected →
        ∃ actual, source.lookup label = some actual) →
      (∀ label actual expected, source.lookup label = some actual →
        target.lookup label = some expected →
        Derivation graph leRow (usable ++ delayed) [] (graph actual) (graph expected)) →
      Derivation graph leRow usable delayed source target

def ContextAt (graph : Graph Row State) (leRow : Row → Row → Prop)
    (depth : Nat) (context : Context Row State) : Prop :=
  ∀ left right, (left, right) ∈ context → At graph leRow depth left right

private theorem context_unlock {usable delayed : Context Row State} {depth previous : Nat}
    (usableValid : ∀ k, k ≤ depth → ContextAt graph leRow k usable)
    (delayedValid : ∀ k, k < depth → ContextAt graph leRow k delayed)
    (smaller : previous < depth) :
    ∀ k, k ≤ previous → ContextAt graph leRow k (usable ++ delayed) := by
  intro k bound left right member
  rcases List.mem_append.mp member with member | member
  · exact usableValid k (Nat.le_trans bound (Nat.le_of_lt smaller)) left right member
  · exact delayedValid k (Nat.lt_of_le_of_lt bound smaller) left right member

private theorem empty_context_at (depth : Nat) :
    ContextAt graph leRow depth [] := by
  intro left right member
  cases member

private theorem eval_record_subtype
    (assignment : State → StructuralBase.Ty Row)
    {source target : Layer Row State}
    (sourceRecord : source.IsRecord) (targetRecord : target.IsRecord)
    (width : ∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual)
    (fields : ∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected →
      StructuralBase.Subtype leRow (assignment actual) (assignment expected)) :
    StructuralBase.Subtype leRow (source.eval assignment) (target.eval assignment) := by
  apply StructuralBase.Subtype.record (Layer.eval_record assignment sourceRecord)
    (Layer.eval_record assignment targetRecord)
  · intro label value found
    rw [Layer.eval_lookup] at found
    cases original : target.lookup label with
    | none => simp [original] at found
    | some expected =>
        obtain ⟨actual, actualFound⟩ := width label expected original
        exact ⟨assignment actual, by simp [Layer.eval_lookup, actualFound]⟩
  · intro label actual expected actualFound expectedFound
    rw [Layer.eval_lookup] at actualFound expectedFound
    cases originalActual : source.lookup label with
    | none => simp [originalActual] at actualFound
    | some a =>
        cases originalExpected : target.lookup label with
        | none => simp [originalExpected] at expectedFound
        | some b =>
            simp only [originalActual, Option.map_some, Option.some.injEq] at actualFound
            simp only [originalExpected, Option.map_some, Option.some.injEq] at expectedFound
            subst actual expected
            exact fields label a b originalActual originalExpected

/-- The guarded induction principle, including arbitrary finite cuts. Delayed
hypotheses must hold strictly below the current observation depth. -/
theorem Derivation.sound_at (depth : Nat) :
    ∀ {usable delayed : Context Row State} {left right : Layer Row State},
    Derivation graph leRow usable delayed left right →
    (∀ k, k ≤ depth → ContextAt graph leRow k usable) →
    (∀ k, k < depth → ContextAt graph leRow k delayed) →
    At graph leRow depth left right := by
  induction depth using Nat.strongRecOn with
  | ind depth smaller =>
      intro usable delayed left right proof
      induction proof with
      | hyp member =>
          intro usableValid _
          exact usableValid depth (Nat.le_refl _) _ _ member
      | assume proof ih =>
          intro usableValid delayedValid
          apply ih usableValid
          intro k bound left right member
          rcases List.mem_cons.mp member with equal | member
          · cases equal
            apply smaller k bound (.assume proof)
            · intro j boundJ
              exact usableValid j (Nat.le_trans boundJ (Nat.le_of_lt bound))
            · intro j boundJ
              exact delayedValid j (Nat.lt_trans boundJ bound)
          · exact delayedValid k bound left right member
      | refl => exact fun _ _ => .refl _
      | trans _ _ ihLeft ihRight =>
          exact fun hu hl => .trans (ihLeft hu hl) (ihRight hu hl)
      | bottom => exact fun _ _ => .bottom _
      | top => exact fun _ _ => .top _
      | unionLeft => exact fun _ _ => .unionLeft _ _
      | unionRight => exact fun _ _ => .unionRight _ _
      | unionElim _ _ ihLeft ihRight =>
          exact fun hu hl => .unionElim (ihLeft hu hl) (ihRight hu hl)
      | interLeft => exact fun _ _ => .interLeft _ _
      | interRight => exact fun _ _ => .interRight _ _
      | interIntro _ _ ihLeft ihRight =>
          exact fun hu hl => .interIntro (ihLeft hu hl) (ihRight hu hl)
      | pair left right _ _ =>
          intro hu hl
          cases depth with
          | zero => exact .pair (.refl _) (.refl _)
          | succ previous =>
              exact .pair
                (smaller previous (by omega) left (context_unlock hu hl (by omega))
                  (fun _ _ => empty_context_at _))
                (smaller previous (by omega) right (context_unlock hu hl (by omega))
                  (fun _ _ => empty_context_at _))
      | variant child _ =>
          intro hu hl
          cases depth with
          | zero => exact .variant (.refl _)
          | succ previous =>
              exact .variant (smaller previous (by omega) child
                (context_unlock hu hl (by omega)) (fun _ _ => empty_context_at _))
      | arrow input inputRow output outputRow _ _ =>
          intro hu hl
          cases depth with
          | zero => exact .arrow (.refl _) inputRow (.refl _) outputRow
          | succ previous =>
              exact .arrow
                (smaller previous (by omega) input (context_unlock hu hl (by omega))
                  (fun _ _ => empty_context_at _)) inputRow
                (smaller previous (by omega) output (context_unlock hu hl (by omega))
                  (fun _ _ => empty_context_at _)) outputRow
      | record sourceRecord targetRecord width fields _ =>
          intro hu hl
          apply eval_record_subtype (observe graph depth) sourceRecord targetRecord width
          intro label actual expected actualFound expectedFound
          cases depth with
          | zero => exact .refl _
          | succ previous =>
              exact smaller previous (by omega) (fields label actual expected actualFound expectedFound)
                (context_unlock hu hl (by omega)) (fun _ _ => empty_context_at _)

/-- Closed declarative cyclic proofs are sound for every finite observation. -/
theorem Derivation.sound {left right : Layer Row State}
    (proof : Derivation graph leRow [] [] left right) :
    Subtype graph leRow left right :=
  fun depth => proof.sound_at depth
    (fun _ _ => empty_context_at _) (fun _ _ => empty_context_at _)

theorem distinct_bases_not_subtypes {left right : Base} (different : left ≠ right) :
    ¬ Subtype graph leRow (.base left) (.base right) :=
  fun proof => StructuralBase.distinct_bases_not_subtypes different (proof 0)

theorem top_not_bottom : ¬ Subtype graph leRow .top .bottom :=
  fun proof => StructuralBase.top_not_bottom (proof 0)

/-- Neither an immediate cyclic hypothesis nor intervening lattice cuts can
make top a subtype of bottom. -/
theorem no_unguarded_top_bottom : ¬ Derivation graph leRow [] [] .top .bottom :=
  fun proof => top_not_bottom proof.sound

/-! ## Conservativity over the existing finite value algebra

Finite trees are an acyclic instance of the graph representation. The following
equivalence is stronger than checking a selection of recursive examples: it
states that the new semantic relation introduces no finite subtype judgments.
-/

/-- Expose lattice and record spines, retaining only guarded children as states. -/
def ofTree : StructuralBase.Ty Row → Layer Row (StructuralBase.Ty Row)
  | .base value => .base value
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (ofTree left) (ofTree right)
  | .inter left right => .inter (ofTree left) (ofTree right)
  | .pair left right => .pair left right
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label value (ofTree rest)
  | .variant label value => .variant label value
  | .arrow input inputRow output outputRow => .arrow input inputRow output outputRow

def treeGraph (Row : Type u) : Graph Row (StructuralBase.Ty Row) := ofTree

@[simp] theorem ofTree_lookup (type : StructuralBase.Ty Row) (label : Nat) :
    (ofTree type).lookup label = type.lookup label := by
  induction type with
  | record name value rest _ ih =>
      by_cases equal : label = name <;>
        simp [ofTree, Layer.lookup, StructuralBase.Ty.lookup, equal, ih]
  | _ => rfl

theorem ofTree_record {type : StructuralBase.Ty Row} (shape : StructuralBase.IsRecord type) :
    (ofTree type).IsRecord := by
  induction shape with
  | empty => exact .empty
  | field _ ih => exact .field ih

theorem observe_tree_mono {left right : StructuralBase.Ty Row}
    (subtype : StructuralBase.Subtype leRow left right) :
    ∀ depth, StructuralBase.Subtype leRow
      (observe (treeGraph Row) depth left) (observe (treeGraph Row) depth right) := by
  induction subtype with
  | refl => exact fun _ => .refl _
  | trans _ _ left right => exact fun depth => .trans (left depth) (right depth)
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
  | unionElim _ _ left right =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .unionElim (left (previous + 1)) (right (previous + 1))
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
  | interIntro _ _ left right =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .interIntro (left (previous + 1)) (right (previous + 1))
  | pair _ _ left right =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .pair (left previous) (right previous)
  | variant _ child =>
      intro depth
      cases depth with
      | zero => exact .refl _
      | succ previous => exact .variant (child previous)
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
            (ofTree_record sourceRecord) (ofTree_record targetRecord)
          · simpa only [ofTree_lookup] using width
          · intro label actual expected actualFound expectedFound
            exact fields label actual expected (by simpa using actualFound)
              (by simpa using expectedFound) previous

/-- A deliberately simple upper bound on the constructor observation depth. -/
def treeBudget : StructuralBase.Ty Row → Nat
  | .base _ | .bottom | .top | .emptyRecord => 1
  | .union left right | .inter left right | .pair left right =>
      treeBudget left + treeBudget right + 1
  | .record _ value rest => treeBudget value + treeBudget rest + 1
  | .variant _ value => treeBudget value + 1
  | .arrow input _ output _ => treeBudget input + treeBudget output + 1

theorem treeBudget_positive (type : StructuralBase.Ty Row) : 0 < treeBudget type := by
  cases type <;> simp only [treeBudget] <;> omega

/-- Finite trees are recovered exactly once the observation budget is enough. -/
theorem observe_tree_exact (type : StructuralBase.Ty Row) (depth : Nat)
    (enough : treeBudget type ≤ depth) : observe (treeGraph Row) depth type = type := by
  induction type generalizing depth with
  | base value =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ => rfl
  | bottom =>
      cases depth <;> rfl
  | top =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ => rfl
  | emptyRecord =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ => rfl
  | union left right ihLeft ihRight =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.union (observe (treeGraph Row) (previous + 1) left)
            (observe (treeGraph Row) (previous + 1) right) = _
          simp only [treeBudget] at enough
          rw [ihLeft _ (by omega), ihRight _ (by omega)]
  | inter left right ihLeft ihRight =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.inter (observe (treeGraph Row) (previous + 1) left)
            (observe (treeGraph Row) (previous + 1) right) = _
          simp only [treeBudget] at enough
          rw [ihLeft _ (by omega), ihRight _ (by omega)]
  | pair left right ihLeft ihRight =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.pair (observe (treeGraph Row) previous left)
            (observe (treeGraph Row) previous right) = _
          simp only [treeBudget] at enough
          rw [ihLeft _ (by omega), ihRight _ (by omega)]
  | record label value rest ihValue ihRest =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.record label (observe (treeGraph Row) previous value)
            (observe (treeGraph Row) (previous + 1) rest) = _
          simp only [treeBudget] at enough
          rw [ihValue _ (by omega), ihRest _ (by omega)]
  | variant label value ihValue =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.variant label (observe (treeGraph Row) previous value) = _
          simp only [treeBudget] at enough
          rw [ihValue _ (by omega)]
  | arrow input inputRow output outputRow ihInput ihOutput =>
      cases depth with
      | zero => simp [treeBudget] at enough
      | succ previous =>
          change StructuralBase.Ty.arrow (observe (treeGraph Row) previous input) inputRow
            (observe (treeGraph Row) previous output) outputRow = _
          simp only [treeBudget] at enough
          rw [ihInput _ (by omega), ihOutput _ (by omega)]

/-- No extra finite constructor distributivity or scalar coercion is introduced. -/
theorem finite_conservative (left right : StructuralBase.Ty Row) :
    Subtype (treeGraph Row) leRow (ofTree left) (ofTree right) ↔
      StructuralBase.Subtype leRow left right := by
  constructor
  · intro proof
    have observed := proof (treeBudget left + treeBudget right)
    change StructuralBase.Subtype leRow
      (observe (treeGraph Row) (treeBudget left + treeBudget right + 1) left)
      (observe (treeGraph Row) (treeBudget left + treeBudget right + 1) right) at observed
    rw [observe_tree_exact left _ (by omega), observe_tree_exact right _ (by omega)] at observed
    exact observed
  · intro proof depth
    exact observe_tree_mono proof (depth + 1)

/-! ## Graph embeddings and finite cyclic witnesses -/

/-- A graph morphism preserves every finite observation, including all row
labels. This permits sharing or duplicating a regular graph, and embedding a
parameter graph in a larger graph before instantiating a scheme. -/
theorem observe_morphism {Target : Type w}
    (target : Graph Row Target) (rename : State → Target)
    (commutes : ∀ state, (graph state).map rename = target (rename state))
    (depth : Nat) (state : State) :
    observe target depth (rename state) = observe graph depth state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [observe, ← commutes, Layer.eval_map]
      congr 1
      funext child
      exact ih child

theorem eval_morphism {Target : Type w}
    (target : Graph Row Target) (rename : State → Target)
    (commutes : ∀ state, (graph state).map rename = target (rename state))
    (depth : Nat) (type : Layer Row State) :
    (type.map rename).eval (observe target depth) = type.eval (observe graph depth) := by
  rw [Layer.eval_map]
  congr 1
  funext child
  exact observe_morphism target rename commutes depth child

/-- Graph embeddings are both sound and reflecting, even when they merge
states. They do not approximate or simplify value or effect components. -/
theorem subtype_morphism {Target : Type w}
    (target : Graph Row Target) (rename : State → Target)
    (commutes : ∀ state, (graph state).map rename = target (rename state))
    (left right : Layer Row State) :
    Subtype target leRow (left.map rename) (right.map rename) ↔ Subtype graph leRow left right := by
  unfold Subtype At
  simp only [eval_morphism target rename commutes]

/-- States 1 and 2 have the same infinite curried-arrow unfolding, with periods
one and two respectively. State 0 is the integer argument. -/
def resultCycle (row : Row) : FiniteGraph Row 4
  | 0 => .base .int
  | 1 => .arrow 0 row 1 row
  | 2 => .arrow 0 row 3 row
  | 3 => .arrow 0 row 2 row

theorem result_cycle_one_two (row : Row) (rowRefl : leRow row row) :
    Derivation (resultCycle row) leRow [] [] (resultCycle row 1) (resultCycle row 2) := by
  apply Derivation.assume
  apply Derivation.arrow .refl rowRefl ?_ rowRefl
  apply Derivation.arrow .refl rowRefl ?_ rowRefl
  exact .hyp (by simp)

theorem result_cycle_two_one (row : Row) (rowRefl : leRow row row) :
    Derivation (resultCycle row) leRow [] [] (resultCycle row 2) (resultCycle row 1) := by
  apply Derivation.assume
  apply Derivation.arrow .refl rowRefl ?_ rowRefl
  apply Derivation.arrow .refl rowRefl ?_ rowRefl
  exact .hyp (by simp)

theorem result_cycles_equivalent (row : Row) (rowRefl : leRow row row) :
    NodeSubtype (resultCycle row) leRow 1 2 ∧ NodeSubtype (resultCycle row) leRow 2 1 :=
  ⟨(result_cycle_one_two row rowRefl).sound, (result_cycle_two_one row rowRefl).sound⟩

/-- Recursion through a function input changes polarity. The two-state graph
records the double unfolding used to give recursive binders a single polarity. -/
def inputCycle (row : Row) : FiniteGraph Row 4
  | 0 => .base .int
  | 1 => .arrow 1 row 0 row
  | 2 => .arrow 3 row 0 row
  | 3 => .arrow 2 row 0 row

theorem input_cycle_one_two (row : Row) (rowRefl : leRow row row) :
    Derivation (inputCycle row) leRow [] [] (inputCycle row 1) (inputCycle row 2) := by
  apply Derivation.assume
  apply Derivation.arrow ?_ rowRefl .refl rowRefl
  apply Derivation.arrow ?_ rowRefl .refl rowRefl
  exact .hyp (by simp)

theorem input_cycle_two_one (row : Row) (rowRefl : leRow row row) :
    Derivation (inputCycle row) leRow [] [] (inputCycle row 2) (inputCycle row 1) := by
  apply Derivation.assume
  apply Derivation.arrow ?_ rowRefl .refl rowRefl
  apply Derivation.arrow ?_ rowRefl .refl rowRefl
  exact .hyp (by simp)

theorem input_cycles_equivalent (row : Row) (rowRefl : leRow row row) :
    NodeSubtype (inputCycle row) leRow 1 2 ∧ NodeSubtype (inputCycle row) leRow 2 1 :=
  ⟨(input_cycle_one_two row rowRefl).sound, (input_cycle_two_one row rowRefl).sound⟩

/-- A recursive arrow is still a usable constructor, not an escape from `any`. -/
theorem top_not_recursive_function (row : Row) :
    ¬ Subtype (inputCycle row) leRow .top (inputCycle row 1) :=
  fun proof => StructuralBase.top_not_arrow _ _ _ _ (proof 0)

end Yulang.RegularValueTypes
