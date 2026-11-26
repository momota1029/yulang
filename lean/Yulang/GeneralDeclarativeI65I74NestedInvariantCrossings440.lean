import Yulang.GeneralDeclarativeI65I74NestedInvariantSource440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open CommonRecursiveNominalIntervals
open CommonDeclaredNominalInspection (Parameter Registry)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Subtype)
open CommonNominalFullDemand (Environment producerLe_iff_probe)
open GeneralNominalCommonBridge (Assignment)

def pointWrap (key : Nat) (e : Endpoint Nat) : Endpoint Nat :=
  .nominal key [.inl (.point e)]

def finiteRows (a b c d : Nat) : List (Atom Nat) :=
  [.tyLe (.var a) (.var b),.tyLe (.var a) (.var d),
    .tyLe (.var c) (.var b),.tyLe (.var c) (.var d)]

def allCrossings (a b c d : Nat) : List (Atom Nat) :=
  finiteRows a b a b ++ finiteRows a b c d ++ finiteRows c d a b ++ finiteRows c d c d

theorem inner_inspect_exact440 {table : Registry} {key : Nat} {p : Parameter}
    (atActual : table[key]? = some [p]) (used : validInner p) (a b c d : Nat) :
    inspectContext table true (nestedInner key a b) (nestedInner key c d) =
      some (finiteRows a b c d) := by
  let left : Bounds (Endpoint Nat) := .interval (loTerm a) (loTerm b)
  let right : Bounds (Endpoint Nat) := .interval (loTerm c) (loTerm d)
  change inspectContext table true (.nominal key [.inl left]) (.nominal key [.inl right]) = _
  have generated : decomposeContextArguments true [p] [.inl left] [.inl right] =
      some [(true,.value (loTerm a) (loTerm b)),(true,.value (loTerm a) (loTerm d)),
        (true,.value (loTerm c) (loTerm b)),(true,.value (loTerm c) (loTerm d))] := by
    rcases used with h|h|h <;> cases h <;> rfl
  rw [inspect_context_nominal _ _ _ _ _ _ _ atActual generated]
  simp only [List.map_cons,List.map_nil,inspectContextObligation,loTerm,inspectContext.eq_def]
  rfl

theorem wrapped_inspect_exact440 {table : Registry} {key : Nat}
    (atActual : table[key]? = some [inv]) (a b : Endpoint Nat) :
    inspectContext table false (pointWrap key a) (pointWrap key b) =
      concatenate [inspectContext table true a a,inspectContext table true a b,
        inspectContext table true b a,inspectContext table true b b] := by
  change inspectContext table false (.nominal key [.inl (.point a)])
    (.nominal key [.inl (.point b)]) = _
  have generated : decomposeContextArguments false [inv] [.inl (.point a)] [.inl (.point b)] =
      some [(true,.value a a),(true,.value a b),(true,.value b a),(true,.value b b)] := rfl
  rw [inspect_context_nominal _ _ _ _ _ _ _ atActual generated]
  rfl

theorem wellformed_inherited_inner440 {table : Registry} {key : Nat} {p : Parameter}
    (atActual : table[key]? = some [p]) (used : validInner p) (a b : Nat) :
    ContextWellFormed table true (nestedInner key a b) := by
  have effective := inherited_value440 used
  refine .nominal atActual (.cons ?_ (.nil true))
  rw [effective.1,effective.2]
  exact .valueInterval (.ordinary true _) (.ordinary true _)

theorem declared_two_original_windows_compile_to_exact_four_families440
    {table : Registry} {outer inner : Nat} {p : Parameter}
    (outerMode : table[outer]? = some [inv]) (innerMode : table[inner]? = some [p])
    (used : validInner p) (a b c d : Nat) :
    compileInContext table false (nestedEndpoint outer inner a b) (nestedEndpoint outer inner c d) =
      some (allCrossings a b c d) := by
  have wf1 : ContextWellFormed table false (nestedEndpoint outer inner a b) :=
    .nominal outerMode (.cons (.valuePoint (wellformed_inherited_inner440 innerMode used a b)) (.nil false))
  have wf2 : ContextWellFormed table false (nestedEndpoint outer inner c d) :=
    .nominal outerMode (.cons (.valuePoint (wellformed_inherited_inner440 innerMode used c d)) (.nil false))
  have adm1 := (admit_context_exact _ _ _).mpr wf1
  have adm2 := (admit_context_exact _ _ _).mpr wf2
  unfold compileInContext
  simp only [adm1,adm2,Bool.and_self,ite_true]
  change inspectContext table false (pointWrap outer (nestedInner inner a b))
    (pointWrap outer (nestedInner inner c d)) = _
  rw [wrapped_inspect_exact440 outerMode,inner_inspect_exact440 innerMode used,
    inner_inspect_exact440 innerMode used,inner_inspect_exact440 innerMode used,
    inner_inspect_exact440 innerMode used]
  simp [allCrossings,concatenate,append,List.append_assoc]

private theorem int_and_float_are_distinct_at_rank_zero440 :
    ¬Subtype (.base .int) .float ∧ ¬Subtype .float (.base .int) := by
  let env : Environment Common.Row := ⟨fun _ => .bottom, fun _ => []⟩
  constructor
  · intro h
    have rel := (producerLe_iff_probe _ _).mp (h 0) 0 env .float trivial
    exact rel
  · intro h
    have rel := (producerLe_iff_probe _ _).mp (h 0) 0 env (.base .int) rfl
    exact rel

/-- The old full-carrier comparison can keep actual Int and Float
meanings in variable slots even though legacy TyTerm lacks a Float literal.
The unexpressed source inference/merger is separate. -/
theorem no_nested_int_float_comparison_in_same_full_assignment440
    {table : Registry} {outer inner : Nat} {p : Parameter}
    (outerMode : table[outer]? = some [inv]) (innerMode : table[inner]? = some [p])
    (used : validInner p) (i f : Nat) (m : Assignment)
    (intAt : (m i).1 = .base .int) (floatAt : (m f).1 = .float) :
    ¬(ContextWellFormed table false (nestedEndpoint outer inner i i) ∧
      ContextWellFormed table false (nestedEndpoint outer inner f f) ∧
      ContextDerives table m false (nestedEndpoint outer inner i i) (nestedEndpoint outer inner f f)) := by
  intro impossible
  have rows := (compiled_full_exact table m false _ _).mpr impossible
  rw [declared_two_original_windows_compile_to_exact_four_families440 outerMode innerMode used,result_some] at rows
  have bad : (Atom.tyLe (.var i) (.var f) : Atom Nat) ∈ allCrossings i i f f :=
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have asserted : Subtype (m i).1 (m f).1 := rows _ bad
  rw [intAt,floatAt] at asserted
  exact int_and_float_are_distinct_at_rank_zero440.1 asserted

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
