import Yulang.GeneralDeclarativeI65I74NestedInvariantCrossings440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open CommonRecursiveNominalIntervals
open CommonDeclaredNominalInspection (Parameter Registry)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype)
open PresenceNormalForm (Atom)

/-- There is no depth parameter in admission or inspection. The caller
    supplies a finite common sequence of actual unary nominal keys. -/
def wrapMany (keys : List Nat) (inner : Endpoint Nat) : Endpoint Nat :=
  keys.foldr pointWrap inner

def inheritedRows : Nat → Nat → Nat → Nat → Nat → List (Atom Nat)
  | 0,a,b,c,d => finiteRows a b c d
  | n+1,a,b,c,d =>
    inheritedRows n a b a b ++ inheritedRows n a b c d ++
    inheritedRows n c d a b ++ inheritedRows n c d c d

def UnaryUsedModes (table : Registry) (keys : List Nat) : Prop :=
  ∀ k ∈ keys, ∃ p : Parameter, table[k]? = some [p] ∧ validInner p

theorem used_wrapper_in_inherited_context440 {table : Registry} {key : Nat} {p : Parameter}
    (source : table[key]? = some [p]) (used : validInner p) (a b : Endpoint Nat) :
    inspectContext table true (pointWrap key a) (pointWrap key b) =
      concatenate [inspectContext table true a a,inspectContext table true a b,
        inspectContext table true b a,inspectContext table true b b] := by
  change inspectContext table true (.nominal key [.inl (.point a)])
    (.nominal key [.inl (.point b)]) = _
  have generated : decomposeContextArguments true [p] [.inl (.point a)] [.inl (.point b)] =
      some [(true,.value a a),(true,.value a b),(true,.value b a),(true,.value b b)] := by
    rcases used with h|h|h <;> cases h <;> rfl
  rw [inspect_context_nominal _ _ _ _ _ _ _ source generated]
  rfl

theorem used_wrapper_admits_inherited440 {table : Registry} {key : Nat} {p : Parameter}
    (source : table[key]? = some [p]) (used : validInner p) {inner : Endpoint Nat}
    (formed : ContextWellFormed table true inner) :
    ContextWellFormed table true (pointWrap key inner) := by
  have mode := inherited_value440 used
  refine .nominal source (.cons ?_ (.nil true))
  rw [mode.1,mode.2]
  exact .valuePoint formed

theorem arbitrary_declared_unary_prefix_preserves_inherited_admission440
    {table : Registry} {keys : List Nat} (author : UnaryUsedModes table keys)
    {input : Endpoint Nat} (formed : ContextWellFormed table true input) :
    ContextWellFormed table true (wrapMany keys input) := by
  induction keys with
  | nil => exact formed
  | cons k ks ih =>
    obtain ⟨mode,found,used⟩ := author k List.mem_cons_self
    exact used_wrapper_admits_inherited440 found used
      (ih (fun j h => author j (List.mem_cons_of_mem _ h)))

theorem arbitrary_unary_prefix_keeps_exact_inherited_crossing_rows440
    {table : Registry} {keys : List Nat} (author : UnaryUsedModes table keys)
    {inner : Nat} {p : Parameter} (source : table[inner]? = some [p]) (used : validInner p)
    (a b c d : Nat) :
    inspectContext table true (wrapMany keys (nestedInner inner a b))
      (wrapMany keys (nestedInner inner c d)) =
      some (inheritedRows keys.length a b c d) := by
  induction keys generalizing a b c d with
  | nil => exact inner_inspect_exact440 source used a b c d
  | cons k ks ih =>
    have rest : UnaryUsedModes table ks := fun j h => author j (List.mem_cons_of_mem _ h)
    obtain ⟨mode,found,active⟩ := author k List.mem_cons_self
    change inspectContext table true
      (pointWrap k (wrapMany ks (nestedInner inner a b)))
      (pointWrap k (wrapMany ks (nestedInner inner c d))) =
      some (inheritedRows (ks.length + 1) a b c d)
    rw [used_wrapper_in_inherited_context440 found active,ih rest,ih rest,ih rest,ih rest]
    simp [inheritedRows,concatenate,append,List.append_assoc]

/-- The outer author can enter invariant context once; every finite count
    of intervening used unary declarations preserves it. The finite
    checker in Entry440 still only reflects its declared syntactic slice. -/
theorem compile_in_context_through_arbitrary_used_nominal_prefix440
    {table : Registry} {keys : List Nat} (author : UnaryUsedModes table keys)
    {outer inner : Nat} {p : Parameter}
    (outside : table[outer]? = some [inv]) (inside : table[inner]? = some [p])
    (used : validInner p) (a b c d : Nat) :
    compileInContext table false (pointWrap outer (wrapMany keys (nestedInner inner a b)))
      (pointWrap outer (wrapMany keys (nestedInner inner c d))) =
      some (inheritedRows (keys.length+1) a b c d) := by
  have wf (x y : Nat) : ContextWellFormed table false
      (pointWrap outer (wrapMany keys (nestedInner inner x y))) :=
    .nominal outside (.cons (.valuePoint
      (arbitrary_declared_unary_prefix_preserves_inherited_admission440 author
        (wellformed_inherited_inner440 inside used x y))) (.nil false))
  unfold compileInContext
  simp only [(admit_context_exact _ _ _).mpr (wf a b),
    (admit_context_exact _ _ _).mpr (wf c d),Bool.and_self,ite_true]
  rw [wrapped_inspect_exact440 outside,
    arbitrary_unary_prefix_keeps_exact_inherited_crossing_rows440 author inside used,
    arbitrary_unary_prefix_keeps_exact_inherited_crossing_rows440 author inside used,
    arbitrary_unary_prefix_keeps_exact_inherited_crossing_rows440 author inside used,
    arbitrary_unary_prefix_keeps_exact_inherited_crossing_rows440 author inside used]
  simp [inheritedRows,concatenate,append,List.append_assoc]


theorem every_depth_has_same_four_distinct_crossing_conditions440 (depth a b c d : Nat)
    (atom : Atom Nat) :
    atom ∈ inheritedRows depth a b c d ↔ atom ∈ finiteRows a b c d := by
  induction depth generalizing a b c d with
  | zero => rfl
  | succ n ih =>
    simp only [inheritedRows,List.mem_append,ih,finiteRows,List.mem_cons,List.not_mem_nil,or_false]
    simp [or_assoc,or_comm,or_left_comm]

theorem actual_emitted_row_count440 (depth a b c d : Nat) :
    (inheritedRows depth a b c d).length = 4 ^ (depth+1) := by
  induction depth generalizing a b c d with
  | zero => rfl
  | succ n ih =>
    simp only [inheritedRows,List.length_append,ih]
    rw [Nat.pow_succ 4 (n+1)]
    omega

theorem arbitrary_used_nominal_prefix_semantic_four_crossings440
    {table : Registry} {keys : List Nat} (author : UnaryUsedModes table keys)
    {outer inner : Nat} {p : Parameter}
    (outside : table[outer]? = some [inv]) (inside : table[inner]? = some [p])
    (used : validInner p) (a b c d : Nat) (m : Assignment) :
    (ContextWellFormed table false (pointWrap outer (wrapMany keys (nestedInner inner a b))) ∧
     ContextWellFormed table false (pointWrap outer (wrapMany keys (nestedInner inner c d))) ∧
     ContextDerives table m false (pointWrap outer (wrapMany keys (nestedInner inner a b)))
        (pointWrap outer (wrapMany keys (nestedInner inner c d)))) ↔
     (Subtype (m a).1 (m b).1 ∧ Subtype (m a).1 (m d).1 ∧
      Subtype (m c).1 (m b).1 ∧ Subtype (m c).1 (m d).1) := by
  rw [← compiled_full_exact table m false _ _,
    compile_in_context_through_arbitrary_used_nominal_prefix440 author outside inside used,result_some]
  simp only [every_depth_has_same_four_distinct_crossing_conditions440,finiteRows,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  rfl

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
