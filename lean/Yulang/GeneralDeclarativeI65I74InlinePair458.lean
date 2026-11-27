import Yulang.GeneralDeclarativeI65I74RoutedInlineVariantEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InlinePair458
open Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm)
open GeneralDeclarativeHead320 (Equation)
open RecordTraversal455.MixedQA (Address)
open CommonRecursiveNominalIntervals (Endpoint)
open InlineVariant458 (Scoped ClosedTail checksScoped scoped_sound458 scoped_complete458
  checksClosedTail tail_sound458 tail_complete458 isNativeInline inline_not_a_named_pointer458 readOrdinaryPayload
  read_ordinary_payload_exact458)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)

inductive At : Address → Endpoint Nat → TyTerm Nat → Prop where
  | pairFirst : At (.primitive .pair 0) (.ordinary (.pair first last)) first
  | pairLast : At (.primitive .pair 1) (.ordinary (.pair first last)) last

def readAt : Address → Endpoint Nat → Option (TyTerm Nat)
  | .primitive .pair 0, .ordinary (.pair x _) => some x
  | .primitive .pair 1, .ordinary (.pair _ y) => some y
  | _,_ => none

theorem exact_native_selected_pair_port458 {addr parent term} :
    readAt addr parent = some term ↔ At addr parent term := by
  constructor
  · intro read
    unfold readAt at read
    split at read
    · cases read; exact .pairFirst
    · cases read; exact .pairLast
    · cases read
  · intro eligible
    cases eligible with
    | pairFirst => rfl
    | pairLast => rfl

open GeneralNominalCenteredHeadMatExpressions (Expr)

def PairAtRaw (row : Equation) (addr : Address) (child : Nat) : Prop :=
  (∃ last, row.right = .primitive .pair [.variable child,.variable last] ∧ addr = .primitive .pair 0) ∨
  (∃ first, row.right = .primitive .pair [.variable first,.variable child] ∧ addr = .primitive .pair 1)

def checkPairAt (row : Equation) (addr : Address) (child : Nat) : Bool :=
  match row.right,addr with
  | .primitive .pair [.variable first,.variable _], .primitive .pair 0 => first == child
  | .primitive .pair [.variable _,.variable last], .primitive .pair 1 => last == child
  | _,_ => false

theorem old_raw_pair_arity_two_and_index_exact458 (row : Equation) (addr : Address) (child : Nat) :
    checkPairAt row addr child = true ↔ PairAtRaw row addr child := by
  constructor
  · intro checked
    unfold checkPairAt at checked
    split at checked
    · rename_i n last raw
      have same : n = child := by simpa using checked
      subst n
      exact .inl ⟨last,raw,rfl⟩
    · rename_i first n raw
      have same : n = child := by simpa using checked
      subst n
      exact .inr ⟨first,raw,rfl⟩
    · cases checked
  · rintro (⟨last,raw,rfl⟩|⟨first,raw,rfl⟩) <;> simp [checkPairAt,raw]

structure Wire where
  parent : Nat
  child : Nat
  childAlias : Link

def ChildReceipt (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Prop :=
  PairAtRaw row addr child ∧ ∃ parent ∈ s.origins, ∃ payload ∈ s.origins, ∃ term,
    At addr parent.endpoint term ∧ Scoped term ∧ (∀ n, term ≠ .var n) ∧
    OriginRoute s parent root ∧ parent.slot = row.left ∧ OriginRoute s payload child ∧
    GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child payload.slot ∧
    parent.issuer = payload.issuer ∧ payload.endpoint = .ordinary term

def check (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) (w : Wire) : Bool := ((do
  let p ← s.origins[w.parent]?
  let o ← s.origins[w.child]?
  let t ← readAt addr p.endpoint
  let selected ← readOrdinaryPayload o.endpoint
  pure (decide (selected = t ∧ p.slot = row.left ∧ p.issuer = o.issuer) &&
    checkPairAt row addr child && checksScoped t && isNativeInline t && checkOriginalRoute s p root &&
      checkOriginalRoute s o child && checksLink s.current.ordinary child o.slot w.childAlias)) : Option Bool).getD false

theorem actual_selected_inline_pair_has_finite_origin_wire458
    (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation) (addr : Address) (child : Nat) :
    (∃ w, check s root row addr child w = true) ↔ ChildReceipt s root row addr child := by
  constructor
  · rintro ⟨w,accept⟩
    cases pRead : s.origins[w.parent]? with
    | none => simp [check,pRead,Option.bind] at accept
    | some parent =>
      cases oRead : s.origins[w.child]? with
      | none => simp [check,pRead,oRead,Option.bind] at accept
      | some selected =>
        cases read : readAt addr parent.endpoint with
        | none => simp [check,pRead,oRead,read,Option.bind] at accept
        | some term =>
          cases oTerm : readOrdinaryPayload selected.endpoint with
          | none => simp [check,pRead,oRead,read,oTerm,Option.bind] at accept
          | some picked =>
            simp only [check,pRead,oRead,read,oTerm,Bind.bind,Option.bind,Pure.pure,
              Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at accept
            obtain ⟨⟨⟨⟨⟨⟨⟨rfl,slot,issuer⟩,layout⟩,eligible⟩,syntax_⟩,parentRoute⟩,selectedRoute⟩,rawAlias⟩ := accept
            exact ⟨(old_raw_pair_arity_two_and_index_exact458 ..).mp layout,parent,List.mem_of_getElem? pRead,selected,List.mem_of_getElem? oRead,picked,
              exact_native_selected_pair_port458.mp read,scoped_sound458 eligible,
              (inline_not_a_named_pointer458 _).mp syntax_,
              (original_route_iff_data455 ..).mp parentRoute,slot,
              (original_route_iff_data455 ..).mp selectedRoute,link rawAlias,issuer,
              read_ordinary_payload_exact458 oTerm⟩
  · rintro ⟨layout,p,wp,o,wo,term,inParent,ok,syn,pr,owner,cr,alias,issuer,endpoint⟩
    obtain ⟨i,first⟩ := List.mem_iff_getElem?.mp wp
    obtain ⟨j,second⟩ := List.mem_iff_getElem?.mp wo
    obtain ⟨w,raw⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
    exact ⟨⟨i,j,w⟩,by simp [check,first,second,exact_native_selected_pair_port458.mpr inParent,
      Option.bind,endpoint,readOrdinaryPayload,(old_raw_pair_arity_two_and_index_exact458 ..).mpr layout,scoped_complete458 ok,(inline_not_a_named_pointer458 _).mpr syn,
      owner,issuer,(original_route_iff_data455 ..).mpr pr,(original_route_iff_data455 ..).mpr cr,raw]⟩

theorem selected_original_payload_has_exact_same_model_native_receipt458
    {s root row addr child} (auth : ChildReceipt s root row addr child)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ p ∈ s.origins, ∃ o ∈ s.origins, ∃ term,
      OriginRoute s p root ∧ OriginRoute s o child ∧ p.issuer = o.issuer ∧
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary child o.slot ∧ m.nativeSyntax row.left = some p.endpoint ∧
      At addr p.endpoint term ∧ m.nativeSyntax o.slot = some (.ordinary term) := by
  obtain ⟨_,p,wp,o,wo,term,atSource,scope,syntax_,pr,owner,cr,alias,issuer,endAt⟩ := auth
  exact ⟨p,wp,o,wo,term,pr,cr,issuer,alias,by simpa only [owner] using fit.2 p wp,
    atSource,by simpa only [endAt] using fit.2 o wo⟩

end Yulang.GeneralDeclarativeI65.I72.InlinePair458
