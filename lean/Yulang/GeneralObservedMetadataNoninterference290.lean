import Yulang.GeneralObservedMetadataAgreement290

/-! A sufficient finite witness for exact equality of the strict auxiliary
publication logic, with the registry and source journal held fixed. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataNoninterference290
open GeneralDeclarations (Registry)
open GeneralNominalInspection (Interpretation)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralObservedMetadataGate290 (preflight context footprint gate)
open GeneralObservedMetadataLive290 (liveKeys)
open GeneralObservedMetadataHistorical290 (qualifies bodyCheck)
open GeneralObservedMetadataSeal290 (Seal dataSeal)
open GeneralObservedMetadataStrict290 (qualifiedTotal strictSeals strictPublish)
open GeneralObservedMetadataEntry290 (LocalEqual agree agree_exact)
open GeneralObservedMetadataAgreement290 (certify_proposal total_proposal)
open GeneralObservedMetadataBook290 (book_exact)

structure Equivalent (r : Registry) (s : State roles) (up down : Occurrence roles)
    (first last : Interpretation) : Prop where
  current : LocalEqual (footprint r s down) r.constructors first r.constructors last
  historical : ∀ e ∈ s.effects, LocalEqual (liveKeys s.core up e.plan)
    r.constructors first r.constructors last

def allKeys (r : Registry) (s : State roles) (up down : Occurrence roles) : List Nat :=
  footprint r s down ++ s.effects.flatMap (fun e : Effect roles => liveKeys s.core up e.plan)

def equivalentCheck (r : Registry) (s : State roles) (up down : Occurrence roles)
    (first last : Interpretation) : Bool :=
  agree (allKeys r s up down) r.constructors first r.constructors last

theorem equivalent_exact (r : Registry) (s : State roles) (up down : Occurrence roles)
    (i j : Interpretation) :
    equivalentCheck r s up down i j = true ↔ Equivalent r s up down i j := by
  unfold equivalentCheck
  rw [agree_exact]
  constructor
  · intro all
    exact ⟨all.restrict (fun _ hk => List.mem_append_left _ hk),
      fun e present => all.restrict (fun _ hk =>
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,present,hk⟩))⟩
  · intro overlap key included
    rcases List.mem_append.mp included with a|b
    · exact overlap.current key a
    · obtain ⟨e,present,hk⟩ := List.mem_flatMap.mp b
      exact overlap.historical e present key hk

theorem gate_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Equivalent r s up down i j) (ask : Offer) :
    gate r s up down ask i = gate r s up down ask j := by
  unfold gate preflight
  rw [certify_proposal h.current]

theorem qualifies_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Equivalent r s up down i j) (ask : Offer)
    (e : Effect roles) (present : e ∈ s.effects) :
    qualifiedTotal r s up down ask i e = qualifiedTotal r s up down ask j e := by
  unfold qualifiedTotal qualifies bodyCheck
  rw [certify_proposal (h.historical e present),total_proposal (h.historical e present)]

theorem seal_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Equivalent r s up down i j) (ask : Offer)
    (e : Effect roles) (present : e ∈ s.effects) :
    dataSeal r s up down ask i e = dataSeal r s up down ask j e := by
  unfold dataSeal
  rw [(book_exact ..).mpr h.current,(book_exact ..).mpr (h.historical e present)]

theorem sealed_lists_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Equivalent r s up down i j) (ask : Offer) :
    strictSeals r s up down ask i = strictSeals r s up down ask j := by
  unfold strictSeals
  rw [gate_unchanged h ask]
  by_cases active : gate r s up down ask j = .receipt .ready
  · rw [ite_eq_left active,ite_eq_left active,
      List.filter_congr (qualifies_unchanged h ask)]
    exact List.map_congr_left (fun e inside => seal_unchanged h ask e (List.mem_filter.mp inside).1)
  · simp [active]

theorem publish_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Equivalent r s up down i j) (ask : Offer) (saved : Seal) :
    strictPublish r s up down ask i saved = strictPublish r s up down ask j saved := by
  unfold strictPublish
  rw [sealed_lists_unchanged h ask]

theorem checked_publish_unchanged {r : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : equivalentCheck r s up down i j = true) (ask : Offer) (saved : Seal) :
    strictPublish r s up down ask i saved = strictPublish r s up down ask j saved :=
  publish_unchanged ((equivalent_exact ..).mp h) ask saved

end Yulang.GeneralObservedMetadataNoninterference290
