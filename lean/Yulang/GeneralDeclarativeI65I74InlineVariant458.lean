import Yulang.GeneralDeclarativeI65I74RoutedReadyMixedEntry457

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InlineVariant458
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)
open RecordTraversal455 (OpenOps)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open GeneralDeclarativeLowerKnown321 (Alias)

mutual
inductive Scoped : TyTerm Nat → Prop where
  | var : Scoped (.var name)
  | base : Scoped (.base b)
  | empty : Scoped .emptyRecord
  | exactEmpty : Scoped .exactEmpty
  | pair : Scoped left → Scoped right → Scoped (.pair left right)
  | variant : Scoped child → Scoped (.variant tag child)
  | record : Scoped child → ClosedTail tail → Scoped (.record label child tail)

inductive ClosedTail : TyTerm Nat → Prop where
  | empty : ClosedTail .emptyRecord
  | field : Scoped child → ClosedTail tail → ClosedTail (.record label child tail)
end

mutual
def checksScoped : TyTerm Nat → Bool
  | .var _ | .base _ | .emptyRecord | .exactEmpty => true
  | .pair x y => checksScoped x && checksScoped y
  | .variant _ t => checksScoped t
  | .record _ x t => checksScoped x && checksClosedTail t
  | _ => false

def checksClosedTail : TyTerm Nat → Bool
  | .emptyRecord => true
  | .record _ x t => checksScoped x && checksClosedTail t
  | _ => false
end

mutual
theorem scoped_sound458 : ∀ {t : TyTerm Nat}, checksScoped t = true → Scoped t
  | .var _, _ => .var
  | .base _, _ => .base
  | .emptyRecord, _ => .empty
  | .exactEmpty, _ => .exactEmpty
  | .pair _ _, ok => .pair (scoped_sound458 (Bool.and_eq_true_iff.mp ok).1)
      (scoped_sound458 (Bool.and_eq_true_iff.mp ok).2)
  | .variant _ _, ok => .variant (scoped_sound458 ok)
  | .record _ _ _, ok => .record (scoped_sound458 (Bool.and_eq_true_iff.mp ok).1)
      (tail_sound458 (Bool.and_eq_true_iff.mp ok).2)
  | .bottom, bad | .top, bad | .union .., bad | .inter .., bad | .required .., bad
  | .recordDefault .., bad | .arrow .., bad => by cases bad

theorem tail_sound458 : ∀ {t : TyTerm Nat}, checksClosedTail t = true → ClosedTail t
  | .emptyRecord, _ => .empty
  | .record _ _ _, ok => .field (scoped_sound458 (Bool.and_eq_true_iff.mp ok).1)
      (tail_sound458 (Bool.and_eq_true_iff.mp ok).2)
  | .var _, bad | .base _, bad | .exactEmpty, bad | .bottom, bad | .top, bad | .union .., bad
  | .inter .., bad | .pair .., bad | .variant .., bad | .required .., bad | .recordDefault .., bad
  | .arrow .., bad => by cases bad
end

mutual
theorem scoped_complete458 : ∀ {t : TyTerm Nat}, Scoped t → checksScoped t = true
  | _, .var | _, .base | _, .empty | _, .exactEmpty => rfl
  | _, .pair x y => Bool.and_eq_true_iff.mpr ⟨scoped_complete458 x,scoped_complete458 y⟩
  | _, @Scoped.variant ch tag x => by
    change checksScoped ch = true
    exact scoped_complete458 x
  | _, .record x y => Bool.and_eq_true_iff.mpr ⟨scoped_complete458 x,tail_complete458 y⟩

theorem tail_complete458 : ∀ {t : TyTerm Nat}, ClosedTail t → checksClosedTail t = true
  | _, .empty => rfl
  | _, .field x y => Bool.and_eq_true_iff.mpr ⟨scoped_complete458 x,tail_complete458 y⟩
end

def isNativeInline : TyTerm Nat → Bool
  | .var _ => false
  | _ => true

theorem inline_not_a_named_pointer458 (t : TyTerm Nat) :
    isNativeInline t = true ↔ ∀ n, t ≠ .var n := by
  cases t <;> simp [isNativeInline]

def readRawVariant : Expr → Option (Nat × Nat)
  | .variant tag (.variable child) => some (tag,child)
  | _ => none

theorem read_raw_variant_exact458 (raw : Expr) (tag child : Nat) :
    readRawVariant raw = some (tag,child) ↔ raw = .variant tag (.variable child) := by
  constructor
  · intro h
    unfold readRawVariant at h
    split at h
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl
    · cases h
  · rintro rfl; rfl

def OriginalInlineVariant (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation) : Prop :=
  ∃ tag child payloadTerm,
    Scoped payloadTerm ∧ (∀ n, payloadTerm ≠ .var n) ∧ row.right = .variant tag (.variable child) ∧
    ∃ parent ∈ s.origins, ∃ payload ∈ s.origins,
      OriginRoute s parent logical ∧ parent.slot = row.left ∧
      OriginRoute s payload child ∧ GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child payload.slot ∧ parent.issuer = payload.issuer ∧
      parent.endpoint = .ordinary (.variant tag payloadTerm) ∧
      payload.endpoint = .ordinary payloadTerm

structure Wire where
  parent : Nat
  payload : Nat
  payloadAlias : Link

def readVariantPayload : CommonRecursiveNominalIntervals.Endpoint Nat → Option (Nat × TyTerm Nat)
  | .ordinary (.variant tag term) => some (tag,term)
  | _ => none

def readOrdinaryPayload : CommonRecursiveNominalIntervals.Endpoint Nat → Option (TyTerm Nat)
  | .ordinary term => some term
  | _ => none

theorem read_variant_payload_exact458
    {point : CommonRecursiveNominalIntervals.Endpoint Nat} {tag term}
    (h : readVariantPayload point = some (tag,term)) :
    point = .ordinary (.variant tag term) := by
  unfold readVariantPayload at h
  split at h
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  · cases h

theorem read_ordinary_payload_exact458
    {point : CommonRecursiveNominalIntervals.Endpoint Nat} {term}
    (h : readOrdinaryPayload point = some term) : point = .ordinary term := by
  cases point <;> cases h <;> rfl

def check (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation)
    (w : Wire) : Bool := ((do
  let (tag,child) ← readRawVariant row.right
  let parent ← s.origins[w.parent]?
  let payload ← s.origins[w.payload]?
  let (sourceTag,ws) ← readVariantPayload parent.endpoint
  let originalWords ← readOrdinaryPayload payload.endpoint
  pure (decide (tag = sourceTag ∧ ws = originalWords ∧ parent.slot = row.left ∧ parent.issuer = payload.issuer) &&
    checksScoped ws && isNativeInline ws &&
    checkOriginalRoute s parent logical && checkOriginalRoute s payload child &&
    checksLink s.current.ordinary child payload.slot w.payloadAlias)) : Option Bool).getD false

theorem linked_inline_variant_has_finite_native_origin_witness458
    (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation) :
    (∃ w, check s logical row w = true) ↔ OriginalInlineVariant s logical row := by
  constructor
  · rintro ⟨w,h⟩
    cases raw : readRawVariant row.right with
    | none => simp [check,raw,Option.bind] at h
    | some choice =>
      rcases choice with ⟨tag,child⟩
      cases lhs : s.origins[w.parent]? with
      | none => simp [check,raw,lhs,Option.bind] at h
      | some parent =>
        cases rhs : s.origins[w.payload]? with
        | none => simp [check,raw,lhs,rhs,Option.bind] at h
        | some payload =>
          cases first : readVariantPayload parent.endpoint with
          | none => simp [check,raw,lhs,rhs,first,Option.bind] at h
          | some pair =>
            rcases pair with ⟨sourceTag,ws⟩
            cases last : readOrdinaryPayload payload.endpoint with
            | none => simp [check,raw,lhs,rhs,first,last,Option.bind] at h
            | some words =>
              simp only [check,raw,lhs,rhs,first,last,Bind.bind,Option.bind,Pure.pure,
                Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at h
              obtain ⟨⟨⟨⟨⟨⟨rfl,rfl,owner,issuer⟩,ne⟩,inline⟩,pRoute⟩,cRoute⟩,rawChild⟩ := h
              exact ⟨_,child,ws,scoped_sound458 ne,(inline_not_a_named_pointer458 _).mp inline,(read_raw_variant_exact458 ..).mp raw,
                parent,List.mem_of_getElem? lhs,payload,List.mem_of_getElem? rhs,
                (original_route_iff_data455 ..).mp pRoute,owner,(original_route_iff_data455 ..).mp cRoute,
                link rawChild,issuer,read_variant_payload_exact458 first,read_ordinary_payload_exact458 last⟩
  · rintro ⟨tag,child,ws,ne,inline,raw,parent,seen1,payload,seen2,pRoute,owner,cRoute,alias,issuer,pTerm,cTerm⟩
    obtain ⟨i,old⟩ := List.mem_iff_getElem?.mp seen1
    obtain ⟨j,new⟩ := List.mem_iff_getElem?.mp seen2
    obtain ⟨aliasWire,aliasOK⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
    refine ⟨⟨i,j,aliasWire⟩,?_⟩
    simp [check,raw,readRawVariant,old,new,Option.bind,pTerm,cTerm,readVariantPayload,
      readOrdinaryPayload,scoped_complete458 ne,(inline_not_a_named_pointer458 _).mpr inline,owner,issuer,
      (original_route_iff_data455 ..).mpr pRoute,(original_route_iff_data455 ..).mpr cRoute,aliasOK]

theorem original_paired_inline_variant_receipt_is_exact_in_every_fit458
    {s : GeneralDeclarativeI65.State} {logical row}
    (actual : OriginalInlineVariant s logical row) (m : I72.Model)
    (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ tag child ws,
      row.right = .variant tag (.variable child) ∧
      m.nativeSyntax row.left = some (.ordinary (.variant tag ws)) ∧
      ∃ payload ∈ s.origins, OriginRoute s payload child ∧
        GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child payload.slot ∧
        m.nativeSyntax payload.slot = some (.ordinary ws) := by
  obtain ⟨tag,child,ws,_,_,raw,parent,seen1,payload,seen2,_,owner,cRoute,plain,_,pTerm,cTerm⟩ := actual
  exact ⟨tag,child,ws,raw,by simpa only [owner,pTerm] using fit.2 parent seen1,
    payload,seen2,cRoute,plain,by simpa only [cTerm] using fit.2 payload seen2⟩

end Yulang.GeneralDeclarativeI65.I72.InlineVariant458
