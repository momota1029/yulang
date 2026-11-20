import Yulang.GeneralObservedMetadataPrimitiveDrift290

/-! Finite extensionality of the actual comparisons and total-body checks.
The proposal's tables may differ outside the scoped list. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataAgreement290
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralObservedMetadataEntry290 (LocalEqual agree entry entry_exact)
open GeneralObservedMetadataLocal290 (primitiveOK primitiveOKAt)
open GeneralObservedMetadataScope290 (certify)
open GeneralObservedMetadataRequestBook290 (requestBook matches_request)
open GeneralObservedMetadataLive290 (liveKeys live_key)
open GeneralObservedMetadataTotal290 (total)
open GeneralObservedMetadataBodies290 (compileFrom compile_eq)
open GeneralNominalCenteredSteps (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)

theorem all_local {α : Type} {xs : List α} {p q : α → Bool} (h : ∀ x ∈ xs, p x = q x) :
    xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.all_cons,h head List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem agree_proposal {keys : List Nat} {actual d e : Constructors} {i j k : Interpretation}
    (h : LocalEqual keys d j e k) : agree keys actual i d j = agree keys actual i e k := by
  apply all_local
  intro x hx
  rw [(entry_exact ..).mpr (h x hx)]

theorem primitive_proposal {keys : List Nat} {d e : Constructors} {j k : Interpretation}
    (h : LocalEqual keys d j e k) : primitiveOK keys d j = primitiveOK keys e k := by
  apply all_local
  intro x hx
  let same := h x hx
  unfold primitiveOKAt
  rw [same.1,same.2.1]

theorem certify_proposal {keys : List Nat} {actual d e : Constructors} {i j k : Interpretation}
    (h : LocalEqual keys d j e k) : certify keys actual i d j = certify keys actual i e k := by
  unfold certify
  rw [agree_proposal h,primitive_proposal h]

theorem total_proposal {s : State roles} {up : Occurrence roles} {plan : Plan roles}
    {c d : Constructors} {i j : Interpretation}
    (h : LocalEqual (liveKeys s up plan) c i d j) :
    total s up plan c i = total s up plan d j := by
  apply all_local
  rintro ⟨out,body⟩ hp
  obtain ⟨request,found⟩ := matches_request.mp hp
  cases body with
  | none => rfl
  | some b =>
    change (compileFrom c i b).isSome = (compileFrom d j b).isSome
    rw [compile_eq b (h.restrict (fun _ read => live_key request found read))]

end Yulang.GeneralObservedMetadataAgreement290
