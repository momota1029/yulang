import Yulang.GeneralDeclarativeI65I74RoutedInlineVariantEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InlineNominalPoint458
open Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm)
open CommonRecursiveNominalIntervals
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)
open RoutedNominalPoint456 (cov actual_declared_use_is_readable456)
open RecordTraversal455.MixedQA (Address)
open InlineVariant458 (Scoped checksScoped scoped_sound458 scoped_complete458 isNativeInline
  inline_not_a_named_pointer458 readOrdinaryPayload read_ordinary_payload_exact458)

def marker (key : Nat) (t : TyTerm Nat) : Endpoint Nat := .nominal key [.inl (.point (.ordinary t))]
def readMarker : Endpoint Nat → Option (Nat × TyTerm Nat)
  | .nominal key [.inl (.point (.ordinary t))] => some (key,t)
  | _ => none

theorem read_marker_exact458 {ep : Endpoint Nat} {key term} :
    readMarker ep = some (key,term) ↔ ep = marker key term := by
  constructor
  · intro seen
    unfold readMarker at seen
    split at seen
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj seen)
      rfl
    · cases seen
  · rintro rfl; rfl

def readRaw : Expr → Option (Nat × Nat)
  | .nominal key [.variable child] => some (key,child)
  | _ => none

theorem read_raw_exact458 {raw : Expr} {key child} :
    readRaw raw = some (key,child) ↔ raw = .nominal key [.variable child] := by
  constructor
  · intro seen
    unfold readRaw at seen
    split at seen
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj seen)
      rfl
    · cases seen
  · rintro rfl; rfl

def HasMode (s : GeneralDeclarativeI65.State) (key : Nat) : Prop :=
  ∃ u : Use s.current.environment key 1, u.mode = .declared [cov] ∧ s.modes[key]? = some [cov]

def checkMode (s : GeneralDeclarativeI65.State) (key : Nat) : Bool :=
  match readUse s.current.environment key 1 with
  | some u =>
    match u.mode with
    | .declared ps => decide (ps = [cov] ∧ s.modes[key]? = some [cov])
    | _ => false
  | none => false

theorem only_actual_covariant_unary_declared_mode458 (s : GeneralDeclarativeI65.State) (key : Nat) :
    checkMode s key = true ↔ HasMode s key := by
  constructor
  · intro ok
    cases sr : readUse s.current.environment key 1 with
    | none => simp [checkMode,sr] at ok
    | some use =>
      cases tag : use.mode with
      | primitive => simp [checkMode,sr,tag] at ok
      | invariant => simp [checkMode,sr,tag] at ok
      | declared ps =>
        have matchMode : ps = [cov] ∧ s.modes[key]? = some [cov] := by
          simpa [checkMode,sr,tag] using ok
        obtain ⟨rfl,table⟩ := matchMode
        exact ⟨use,tag,table⟩
  · rintro ⟨use,mode,table⟩
    simp [checkMode,actual_declared_use_is_readable456 use mode,mode,table]

structure Wire where
  parent : Nat
  child : Nat
  childAlias : Link

def NominalReceipt (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Prop :=
  ∃ key t, addr = .nominal key 0 ∧ row.right = .nominal key [.variable child] ∧
    HasMode s key ∧ Scoped t ∧ (∀ n, t ≠ .var n) ∧
    ∃ p ∈ s.origins, ∃ o ∈ s.origins, p.slot = row.left ∧ OriginRoute s p root ∧
      OriginRoute s o child ∧ GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child o.slot ∧
      p.issuer = o.issuer ∧ p.endpoint = marker key t ∧ o.endpoint = .ordinary t

def check (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation) (addr : Address)
    (child : Nat) (w : Wire) : Bool := ((do
  let (k,n) ← readRaw row.right
  let p ← s.origins[w.parent]?
  let o ← s.origins[w.child]?
  let (source,t) ← readMarker p.endpoint
  let selected ← readOrdinaryPayload o.endpoint
  pure (decide (n = child ∧ addr = .nominal k 0 ∧ k = source ∧ t = selected ∧
    p.slot = row.left ∧ p.issuer = o.issuer) && checkMode s k && checksScoped t && isNativeInline t &&
    checkOriginalRoute s p root && checkOriginalRoute s o child &&
    checksLink s.current.ordinary child o.slot w.childAlias)) : Option Bool).getD false

theorem inline_point_exact_receipt_is_finite458
    (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation) (addr : Address) (child : Nat) :
    (∃ w, check s root row addr child w = true) ↔ NominalReceipt s root row addr child := by
  constructor
  · rintro ⟨w,ok⟩
    cases raw : readRaw row.right <;> simp [check,raw,Option.bind] at ok
    rename_i r
    obtain ⟨key,n⟩ := r
    cases a : s.origins[w.parent]? <;> simp [a] at ok
    rename_i p
    cases b : s.origins[w.child]? <;> simp [b] at ok
    rename_i o
    cases markerRead : readMarker p.endpoint <;> simp [markerRead] at ok
    rename_i query
    obtain ⟨source,t⟩ := query
    cases sourceRead : readOrdinaryPayload o.endpoint <;> simp [sourceRead] at ok
    rename_i term
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl,rfl,rfl,rfl,slot,issuer⟩,m⟩,sc⟩,inline⟩,pRoute⟩,oRoute⟩,rawLink⟩ := ok
    exact ⟨_,_,rfl,read_raw_exact458.mp raw,(only_actual_covariant_unary_declared_mode458 _ _).mp m,
      scoped_sound458 sc,(inline_not_a_named_pointer458 _).mp inline,
      p,List.mem_of_getElem? a,o,List.mem_of_getElem? b,slot,
      (original_route_iff_data455 ..).mp pRoute,(original_route_iff_data455 ..).mp oRoute,
      link rawLink,issuer,read_marker_exact458.mp markerRead,read_ordinary_payload_exact458 sourceRead⟩
  · rintro ⟨key,t,rfl,raw,mode,sc,inline,p,pMember,o,oMember,slot,pRoute,oRoute,alias,issuer,read,last⟩
    obtain ⟨i,pThere⟩ := List.mem_iff_getElem?.mp pMember
    obtain ⟨j,oThere⟩ := List.mem_iff_getElem?.mp oMember
    obtain ⟨edge,rawLink⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
    exact ⟨⟨i,j,edge⟩,by simp [check,read_raw_exact458.mpr raw,pThere,oThere,read_marker_exact458.mpr read,
      last,readOrdinaryPayload,Option.bind,slot,issuer,(only_actual_covariant_unary_declared_mode458 _ _).mpr mode,
      scoped_complete458 sc,(inline_not_a_named_pointer458 _).mpr inline,
      (original_route_iff_data455 ..).mpr pRoute,(original_route_iff_data455 ..).mpr oRoute,rawLink]⟩

open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (subtype_refl)

def comparisonAtoms (context : Bool) (t : TyTerm Nat) : List (Atom Nat) :=
  List.replicate (if context then 4 else 1) (.tyLe t t)

theorem same_original_inline_point_compiles_exact_self_atoms458
    {s : GeneralDeclarativeI65.State} {key} (t : TyTerm Nat) (mode : HasMode s key) (context : Bool) :
    compileInContext s.modes context (marker key t) (marker key t) =
      some (comparisonAtoms context t) := by
  obtain ⟨_,_,table⟩ := mode
  cases context with
  | false =>
    have wf : ContextWellFormed s.modes false (marker key t) :=
      .nominal table (.cons (.valuePoint (.ordinary false _)) (.nil false))
    have a := (admit_context_exact _ _ _).mpr wf
    have runs : decomposeContextArguments false [cov] [.inl (.point (.ordinary t))]
        [.inl (.point (.ordinary t))] = some [(false,.value (.ordinary t) (.ordinary t))] := rfl
    unfold compileInContext
    simp only [a,Bool.and_self,ite_true]
    change inspectContext s.modes false (.nominal key [.inl (.point (.ordinary t))])
      (.nominal key [.inl (.point (.ordinary t))]) = _
    rw [inspect_context_nominal _ _ _ _ _ _ _ table runs]
    simp only [List.map_cons,List.map_nil,inspectContextObligation,inspectContext.eq_def]
    rfl
  | true =>
    have wf : ContextWellFormed s.modes true (marker key t) :=
      .nominal table (.cons (.valuePoint (.ordinary true _)) (.nil true))
    have a := (admit_context_exact _ _ _).mpr wf
    have runs : decomposeContextArguments true [cov] [.inl (.point (.ordinary t))]
        [.inl (.point (.ordinary t))] =
        some [(true,.value (.ordinary t) (.ordinary t)),(true,.value (.ordinary t) (.ordinary t)),
          (true,.value (.ordinary t) (.ordinary t)),(true,.value (.ordinary t) (.ordinary t))] := rfl
    unfold compileInContext
    simp only [a,Bool.and_self,ite_true]
    change inspectContext s.modes true (.nominal key [.inl (.point (.ordinary t))])
      (.nominal key [.inl (.point (.ordinary t))]) = _
    rw [inspect_context_nominal _ _ _ _ _ _ _ table runs]
    simp only [List.map_cons,List.map_nil,inspectContextObligation,inspectContext.eq_def]
    rfl

theorem inline_point_keeps_original_same_fit_and_declared_context458
    {s root row addr child} (actual : NominalReceipt s root row addr child)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ k t o, addr = .nominal k 0 ∧ m.nativeSyntax row.left = some (marker k t) ∧
      OriginRoute s o child ∧ GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child o.slot ∧
      m.nativeSyntax o.slot = some (.ordinary t) ∧ ∀ (context : Bool),
        ContextWellFormed s.modes context (marker k t) ∧
        ContextDerives s.modes m.assignment context (marker k t) (marker k t) := by
  obtain ⟨k,t,atPort,_,mode,_,_,p,pAt,o,oAt,slot,_,route,alias,_,parent,childRead⟩ := actual
  refine ⟨k,t,o,atPort,by simpa [slot,parent] using fit.2 p pAt,route,alias,
    by simpa [childRead] using fit.2 o oAt,?_⟩
  intro context
  have refl_ := compiled_full_exact s.modes m.assignment context (marker k t) (marker k t)
  rw [same_original_inline_point_compiles_exact_self_atoms458 t mode context,result_some] at refl_
  obtain ⟨wf,_,cmp⟩ := refl_.mp (by
    intro atom member
    have exact := List.eq_of_mem_replicate member
    subst atom
    exact subtype_refl _)
  exact ⟨wf,cmp⟩

end Yulang.GeneralDeclarativeI65.I72.InlineNominalPoint458
