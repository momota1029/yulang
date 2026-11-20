import Yulang.GeneralObservedMetadataOldCongr290

/-! Both proposed constructor and interpretation entries may vary off the
scope, provided the declarations and raw journal are held fixed. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataRegistryCongr290
open GeneralDeclarations (Registry)
open GeneralNominalInspection (Interpretation)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptCatalogue289 (constructorKeys)
open GeneralRebaseReceiptExactLink289 (exactProducer)
open GeneralObservedMetadataGate290 (preflight context footprint gate)
open GeneralObservedMetadataScope290 (coverage)
open GeneralObservedMetadataHistorical290 (qualifies bodyCheck)
open GeneralObservedMetadataLive290 (liveKeys)
open GeneralObservedMetadataSeal290 (Seal dataSeal)
open GeneralObservedMetadataStrict290 (qualifiedTotal strictSeals strictPublish)
open GeneralObservedMetadataNoninterference290 (allKeys)
open GeneralObservedMetadataEntry290 (LocalEqual agree agree_exact)
open GeneralObservedMetadataBook290 (book_exact)
open GeneralObservedMetadataAgreement290 (certify_proposal total_proposal)
open GeneralObservedMetadataOldCongr290 (candidate_world same_decision compare_first)

structure Comparable (r q : Registry) (s : State roles) (up down : Occurrence roles)
    (i j : Interpretation) : Prop where
  world : r.declarations = q.declarations
  tables : LocalEqual (allKeys r s up down) r.constructors i q.constructors j

def compare (r q : Registry) (s : State roles) (up down : Occurrence roles)
    (i j : Interpretation) : Bool :=
  decide (r.declarations = q.declarations) && agree (allKeys r s up down) r.constructors i q.constructors j

theorem compare_exact (r q : Registry) (s : State roles) (up down : Occurrence roles)
    (i j : Interpretation) : compare r q s up down i j = true ↔ Comparable r q s up down i j := by
  unfold compare
  simp only [Bool.and_eq_true,decide_eq_true_eq,agree_exact]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.world,h.tables⟩⟩

theorem same_footprint {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) :
    footprint r s down = footprint q s down := by
  unfold footprint
  rw [candidate_world h.world down]

theorem current {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) :
    LocalEqual (footprint r s down) r.constructors i q.constructors j :=
  h.tables.restrict (fun _ found => List.mem_append_left _ found)

theorem past {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j)
    {e : Effect roles} (recorded : e ∈ s.effects) :
    LocalEqual (liveKeys s.core up e.plan) r.constructors i q.constructors j :=
  h.tables.restrict (fun _ found => List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,recorded,found⟩))

theorem descriptors {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) :
    ∀ key ∈ constructorKeys (context s).state, r.constructors key = q.constructors key :=
  fun key seen => (current h key (List.mem_append_left _ seen)).1

theorem gate_same {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) (ask : Offer) :
    gate r s up down ask i = gate q s up down ask j := by
  unfold gate preflight
  rw [← same_footprint h,certify_proposal (current h),same_decision s up down ask h.world (descriptors h)]

theorem candidate_same {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) (ask : Offer)
    {e : Effect roles} (recorded : e ∈ s.effects) :
    qualifiedTotal r s up down ask i e = qualifiedTotal q s up down ask j e := by
  unfold qualifiedTotal qualifies bodyCheck exactProducer
  rw [compare_first (descriptors h),certify_proposal (past h recorded),total_proposal (past h recorded)]

theorem data_same {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) (ask : Offer)
    {e : Effect roles} (recorded : e ∈ s.effects) :
    dataSeal r s up down ask i e = dataSeal q s up down ask j e := by
  unfold dataSeal
  rw [← same_footprint h,(book_exact ..).mpr (current h),(book_exact ..).mpr (past h recorded)]

theorem equal_permitted {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : Comparable r q s up down i j) (ask : Offer) :
    strictSeals r s up down ask i = strictSeals q s up down ask j := by
  unfold strictSeals
  rw [gate_same h ask]
  by_cases live : gate q s up down ask j = .receipt .ready
  · rw [ite_eq_left live,ite_eq_left live,List.filter_congr (fun e hz => candidate_same h ask (e := e) hz)]
    exact List.map_congr_left (fun _ hz => data_same h ask (List.mem_filter.mp hz).1)
  · simp [live]

theorem equal_publish {r q : Registry} {s : State roles} {up down : Occurrence roles}
    {i j : Interpretation} (h : compare r q s up down i j = true) (ask : Offer)
    (saved : Seal) :
    strictPublish r s up down ask i saved = strictPublish q s up down ask j saved := by
  unfold strictPublish
  rw [equal_permitted ((compare_exact ..).mp h) ask]

end Yulang.GeneralObservedMetadataRegistryCongr290
