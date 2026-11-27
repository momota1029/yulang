import Yulang.GeneralDeclarativeI65I74RoutedMixedEntry456
import Yulang.GeneralDeclarativeI65NativePrefixCore377
import Yulang.GeneralDeclarativeWitnessFullIntervals357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedNominalPoint456
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessConstructorModes357 (Use SourceMode readUse readMode Layout)
open CommonRecursiveNominalIntervals (Argument Endpoint Bounds decomposeContextArgument effectiveParameter)
open CommonDeclaredNominalInspection (Parameter)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)
open RecordTrail455.MixedNative456 (extraOpenOps)
open RecordTraversal455 (OpenOps)

def cov : Parameter := ⟨.value,.covariant⟩
def pointArg (n : Nat) : Argument Nat := .inl (.point (.ordinary (.var n)))
def marker (key child : Nat) : Endpoint Nat := .nominal key [pointArg child]

theorem exact_readMode_of_independent_declared456 {e name ps} (real : SourceMode e name (.declared ps)) :
    readMode e name = some ⟨.declared ps,real⟩ := by
  cases real with
  | declared pos noPrim noInv =>
    unfold readMode
    split
    · rename_i ys picked
      have same := Option.some.inj (picked.symm.trans pos)
      subst ys
      split <;> simp_all
    · rename_i absent
      have bad := pos.symm.trans absent
      cases bad

theorem actual_declared_use_is_readable456 {e key arity ps} (real : Use e key arity)
    (mode : real.mode = .declared ps) : readUse e key arity = some real := by
  have read : readMode e key = some ⟨real.mode,real.sourced⟩ := by
    have source := exact_readMode_of_independent_declared456 (mode ▸ real.sourced)
    exact source.trans (congrArg some (Subtype.ext mode.symm))
  have checks := And.intro real.declaredName (And.intro real.currentName
    (And.intro real.sameLayout (And.intro real.exactArity real.kinded)))
  unfold readUse
  split
  · split
    · rename_i wrote live fullW fullL
      have eqW := Option.some.inj (fullW.symm.trans real.actual)
      have eqL := Option.some.inj (fullL.symm.trans real.snapshot)
      subst wrote
      subst live
      simp [Bind.bind,Option.bind,read,checks]
    · rename_i missing
      exact (missing _ _ real.actual real.snapshot).elim
  · rename_i absent
    exact (absent real.noDefault).elim

def checkMarker (key child : Nat) : Endpoint Nat → Bool
  | .nominal k [.inl (.point (.ordinary (.var n)))] => (k == key) && (n == child)
  | _ => false

theorem check_marker_exact (key child) (ep : Endpoint Nat) :
    checkMarker key child ep = true ↔ ep = marker key child := by
  constructor
  · intro valid
    unfold checkMarker at valid
    split at valid
    · rename_i k n
      obtain ⟨rfl,rfl⟩ : k = key ∧ n = child := by simpa [Bool.and_eq_true] using valid
      rfl
    · cases valid
  · rintro rfl
    simp [marker,pointArg,checkMarker]

structure Opened (s : GeneralDeclarativeI65.State) (logical : Nat) (r : Equation) where
  key : Nat
  child : Nat
  origin : Origin
  authored : origin ∈ s.origins
  original : OriginRoute s origin logical
  physical : origin.slot = r.left
  endpoint : origin.endpoint = marker key child
  raw : r.right = .nominal key [.variable child]
  use : Use s.current.environment key 1
  mode : use.mode = .declared [cov]
  table : s.modes[key]? = some [cov]

def atNominal (s : GeneralDeclarativeI65.State) (logical : Nat) (r : Equation)
    (index : Nat) : Option (Opened s logical r) :=
  match raw : r.right with
  | .nominal key [.variable child] =>
    match src : s.origins[index]? with
    | none => none
    | some o =>
      if auth : checkOriginalRoute s o logical = true ∧ o.slot = r.left ∧
        checkMarker key child o.endpoint = true then
        match readUse s.current.environment key 1 with
        | none => none
        | some used =>
          match wm : used.mode with
          | .declared params =>
            if chosen : params = [cov] ∧ s.modes[key]? = some [cov] then
              some ⟨key,child,o,List.mem_of_getElem? src,
                (original_route_iff_data455 ..).mp auth.1,auth.2.1,(check_marker_exact ..).mp auth.2.2,
                raw,used,wm.trans (congrArg _ chosen.1),chosen.2⟩
            else none
          | _ => none
      else none
  | _ => none

theorem actual_covariant_nominal_has_finite_origin_wire456
    {s logical r} (p : Opened s logical r) :
    ∃ i, (atNominal s logical r i).isSome = true := by
  obtain ⟨index,src⟩ := List.mem_iff_getElem?.mp p.authored
  have original := (original_route_iff_data455 ..).mpr p.original
  have read := actual_declared_use_is_readable456 p.use p.mode
  refine ⟨index,?_⟩
  unfold atNominal
  split
  · rename_i key child known
    have sameKey : key = p.key := (Expr.nominal.inj (known.symm.trans p.raw)).1
    have sameChild : child = p.child := Expr.variable.inj
      (List.singleton_inj.mp (Expr.nominal.inj (known.symm.trans p.raw)).2)
    subst key
    subst child
    split
    · rename_i absent
      rw [src] at absent
      cases absent
    · rename_i origin found
      have eq := Option.some.inj (found.symm.trans src)
      subst origin
      simp [original,p.physical,(check_marker_exact ..).mpr p.endpoint,read]
      split
      · rename_i params picked
        have paramEq := GeneralDeclarativeWitnessConstructorModes357.Mode.declared.inj (picked.symm.trans p.mode)
        subst params
        simp [p.table]
      · rename_i noMode
        exact (noMode _ p.mode).elim
  · rename_i noShape
    exact (noShape _ _ p.raw).elim

theorem finite_original_wire_iff_actual_covariant_nominal456 (s : GeneralDeclarativeI65.State)
    (logical : Nat) (r : Equation) :
    (∃ i, (atNominal s logical r i).isSome = true) ↔ Nonempty (Opened s logical r) := by
  constructor
  · rintro ⟨i,accepted⟩
    cases h : atNominal s logical r i with
    | none => simp [h] at accepted
    | some p => exact ⟨p⟩
  · rintro ⟨p⟩
    exact actual_covariant_nominal_has_finite_origin_wire456 p

def nominalOps (s : GeneralDeclarativeI65.State) : OpenOps where
  Token := Nat
  allowed := fun root row => (extraOpenOps s).allowed root row ∨ Nonempty (Opened s root row)
  check := fun root row i => (extraOpenOps s).check root row i || (atNominal s root row i).isSome
  exactCheck := by
    intro root row
    rw [← (extraOpenOps s).exactCheck,← finite_original_wire_iff_actual_covariant_nominal456]
    constructor
    · rintro ⟨w,yes⟩
      rcases Bool.or_eq_true_iff.mp yes with a|b
      · exact .inl ⟨w,a⟩
      · exact .inr ⟨w,b⟩
    · rintro (⟨w,a⟩|⟨w,b⟩)
      · exact ⟨w,Bool.or_eq_true_iff.mpr (.inl a)⟩
      · exact ⟨w,Bool.or_eq_true_iff.mpr (.inr b)⟩

theorem selected_point_uses_the_original_coordinate_in_both_contexts456
    {s logical r} (p : Opened s logical r) (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    m.nativeSyntax r.left = some (marker p.key p.child) ∧
    decomposeContextArgument false cov (pointArg p.child) (pointArg p.child) =
      some [(false,.value (.ordinary (.var p.child)) (.ordinary (.var p.child)))] ∧
    decomposeContextArgument true cov (pointArg p.child) (pointArg p.child) =
      some [(true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
        (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
        (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
        (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child)))] := by
  exact ⟨by simpa only [p.physical,p.endpoint] using fit.2 p.origin p.authored,rfl,rfl⟩

open CommonRecursiveNominalIntervals
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (subtype_refl)

def selfComparisons (context : Bool) (site : Nat) : List (Atom Nat) :=
  List.replicate (if context then 4 else 1) (.tyLe (.var site) (.var site))

theorem original_point_comparison_is_exact456 {s logical r} (p : Opened s logical r) (context : Bool) :
    compileInContext s.modes context (marker p.key p.child) (marker p.key p.child) =
      some (selfComparisons context p.child) := by
  cases context with
  | false =>
    have wf : ContextWellFormed s.modes false (marker p.key p.child) :=
      .nominal p.table (.cons (.valuePoint (.ordinary false _)) (.nil false))
    have a := (admit_context_exact _ _ _).mpr wf
    have runs : decomposeContextArguments false [cov] [pointArg p.child] [pointArg p.child] =
        some [(false,.value (.ordinary (.var p.child)) (.ordinary (.var p.child)))] := rfl
    unfold compileInContext
    simp only [a,Bool.and_self,ite_true]
    change inspectContext s.modes false (.nominal p.key [pointArg p.child])
      (.nominal p.key [pointArg p.child]) = _
    rw [inspect_context_nominal _ _ _ _ _ _ _ p.table runs]
    simp only [List.map_cons,List.map_nil,inspectContextObligation,inspectContext.eq_def]
    rfl
  | true =>
    have wf : ContextWellFormed s.modes true (marker p.key p.child) :=
      .nominal p.table (.cons (.valuePoint (.ordinary true _)) (.nil true))
    have a := (admit_context_exact _ _ _).mpr wf
    have runs : decomposeContextArguments true [cov] [pointArg p.child] [pointArg p.child] =
        some [(true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
          (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
          (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child))),
          (true,.value (.ordinary (.var p.child)) (.ordinary (.var p.child)))] := rfl
    unfold compileInContext
    simp only [a,Bool.and_self,ite_true]
    change inspectContext s.modes true (.nominal p.key [pointArg p.child])
      (.nominal p.key [pointArg p.child]) = _
    rw [inspect_context_nominal _ _ _ _ _ _ _ p.table runs]
    simp only [List.map_cons,List.map_nil,inspectContextObligation,inspectContext.eq_def]
    rfl

theorem original_point_compares_in_the_same_model456 {s logical r} (p : Opened s logical r)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) (context : Bool) :
    m.nativeSyntax r.left = some (marker p.key p.child) ∧
      ContextWellFormed s.modes context (marker p.key p.child) ∧
      ContextDerives s.modes m.assignment context (marker p.key p.child) (marker p.key p.child) := by
  refine ⟨(selected_point_uses_the_original_coordinate_in_both_contexts456 p m fit).1,?_⟩
  have hs := compiled_full_exact s.modes m.assignment context (marker p.key p.child)
    (marker p.key p.child)
  rw [original_point_comparison_is_exact456 p context,result_some] at hs
  obtain ⟨wf,_,comparison⟩ := hs.mp (by
    intro atom mem
    have exact := (List.eq_of_mem_replicate mem)
    subst atom
    exact subtype_refl _ )
  exact ⟨wf,comparison⟩

open RecordTraversal455.MixedQA (Address ChildAt)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)

theorem literal_covariant_point_child_is_only_original_ordinal456
    {s logical r} (p : Opened s logical r) {sh : Shape} {code address child next}
    (head : shapeOf r.right = some sh) (actual : ChildAt sh code address child next) :
    address = .nominal p.key 0 ∧ child = p.child ∧
      ∃ written, code = .nominal p.key written ∧ written[0]? = some next := by
  have shape : sh = .nominal p.key [p.child] := by
    rw [p.raw] at head
    exact (Option.some.inj head).symm
  subst sh
  cases actual with
  | @nominal xs i x ps q key rawAt writtenAt =>
    have first : i = 0 := by
      have bound := (List.getElem?_eq_some_iff.mp rawAt).1
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
    subst i
    exact ⟨rfl,(Option.some.inj rawAt).symm,ps,rfl,writtenAt⟩

end Yulang.GeneralDeclarativeI65.I72.RoutedNominalPoint456
