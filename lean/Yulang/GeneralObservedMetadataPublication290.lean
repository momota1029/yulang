import Yulang.GeneralObservedMetadataSeal290

/-! Two pure stages: issue the first currently supported finite seal, then
revalidate a saved seal against every actual source check before compiling
a mark. This is auxiliary readback, never a mutation of the raw journal. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataPublication290
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalInspection (Interpretation)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptCompile289 (Mark compile)
open GeneralObservedMetadataSeal290 (Seal seals membership_implies_historical kept_has_reference_books)

def issue (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (proposal : Interpretation) : Option Seal :=
  (seals r s up down ask proposal).head?

inductive Output where
  | staleOrUnsupported
  | noMark
  | released (code : Mark)
  deriving Repr, DecidableEq

def publishFrom (permitted : List Seal) (up : Occurrence roles) (ask : Offer) (saved : Seal) : Output :=
  if saved ∈ permitted then
    match compile up ask with
    | none => .noMark
    | some code => .released code
  else .staleOrUnsupported

def publish (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (proposal : Interpretation) (saved : Seal) : Output :=
  publishFrom (seals r s up down ask proposal) up ask saved

theorem publishFrom_exact (permitted : List Seal) (up : Occurrence roles) (ask : Offer) (saved : Seal)
    (value : Mark) :
    publishFrom permitted up ask saved = .released value ↔
      saved ∈ permitted ∧ compile up ask = some value := by
  by_cases fresh : saved ∈ permitted
  · unfold publishFrom
    rw [ite_eq_left fresh]
    cases compile up ask <;> simp [fresh]
  · simp [publishFrom,fresh]

theorem stale_exact (permitted : List Seal) (up : Occurrence roles) (ask : Offer) (saved : Seal) :
    publishFrom permitted up ask saved = .staleOrUnsupported ↔ saved ∉ permitted := by
  unfold publishFrom
  by_cases fresh : saved ∈ permitted
  · rw [ite_eq_left fresh]
    cases compile up ask <;> simp [fresh]
  · simp [fresh]

theorem issue_is_current {r : Registry} {s : State roles} {up down : Occurrence roles} {ask : Offer}
    {proposal : Interpretation} {saved : Seal} (issued : issue r s up down ask proposal = some saved) :
    saved ∈ seals r s up down ask proposal := by
  unfold issue at issued
  cases found : seals r s up down ask proposal with
  | nil => rw [found] at issued; cases issued
  | cons first rest =>
    rw [found] at issued
    exact (Option.some.inj issued) ▸ List.mem_cons_self

theorem ready_release {r : Registry} {s : State roles} {up down : Occurrence roles} {ask : Offer}
    {proposal : Interpretation} {saved : Seal} {value : Mark}
    (published : publish r s up down ask proposal saved = .released value) :
    GeneralObservedMetadataHistorical290.resolve r s up down ask proposal = .prior (.receipt .ready) ∧
    value.target = ask.output := by
  obtain ⟨inList,compiled⟩ := (publishFrom_exact _ _ _ _ _).mp published
  exact ⟨membership_implies_historical inList,
    GeneralRebaseReceiptCompile289.compile_has_offered_target up ask value compiled⟩

end Yulang.GeneralObservedMetadataPublication290
