import Yulang.GeneralSourceMetadataPublication291

/-! Prove exactly the catalogue obligation of a metadata-only view.
The new catalogue is generated from source; every other state field is
the original one. No journal installation is synthesized. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataSnapshot291
open GeneralSourceMetadataRows291 (Source constructors interpretation)
open GeneralNominalState (State Descriptor Models Known Linked)
open GeneralObservedMetadataScope290 (descriptor_key)
open GeneralRebaseReceiptCatalogue289 (constructorKeys agreement agreement_exact)
open GeneralNominalCandidates (Context)
open GeneralNominalCommonBridge (Assignment)

def Fits (state : State) (src : Source) : Prop :=
  ∀ slot desc, state.nominals slot = some desc →
    constructors src desc.constructor = some desc.declaration

def check (state : State) (src : Source) : Bool :=
  agreement (constructorKeys state) (constructors src) state.constructors

theorem descriptor_present (state : State) (key : Nat) (observed : key ∈ constructorKeys state) :
    ∃ slot desc, state.nominals slot = some desc ∧ desc.constructor = key := by
  unfold constructorKeys at observed
  obtain ⟨entry,seen,asKey⟩ := List.mem_filterMap.mp observed
  obtain ⟨slot,where_⟩ := List.mem_ofFn.mp seen
  change (state.nominals slot).map Descriptor.constructor = entry at where_
  cases item : state.nominals slot with
  | none =>
    rw [item] at where_
    cases where_
    cases asKey
  | some d =>
    rw [item] at where_
    cases where_
    exact ⟨slot,d,item,Option.some.inj asKey⟩

theorem check_exact (state : State) (src : Source) : check state src = true ↔ Fits state src := by
  unfold check Fits
  rw [agreement_exact]
  constructor
  · intro agrees slot d captured
    exact (agrees d.constructor (descriptor_key state slot d captured)).trans (state.catalogue slot d captured)
  · intro fits key seen
    obtain ⟨slot,d,captured,rfl⟩ := descriptor_present state key seen
    exact (fits slot d captured).trans (state.catalogue slot d captured).symm

def retag (state : State) (src : Source) (fits : Fits state src) : State :=
  { state with constructors := constructors src, catalogue := fits }

def context (state : State) (src : Source) (fits : Fits state src) : Context :=
  ⟨retag state src fits,interpretation src⟩

theorem model_preserved (state : State) (src : Source) (fits : Fits state src) (m : Assignment) :
    Models (retag state src fits) m ↔ Models state m := Iff.rfl

theorem known_preserved (state : State) (src : Source) (fits : Fits state src) (slot : Nat) :
    Known (retag state src fits) slot ↔ Known state slot := Iff.rfl

theorem link_preserved (state : State) (src : Source) (fits : Fits state src)
    (demand : GeneralSourceState.Demand roles) :
    Linked (retag state src fits) demand ↔ Linked state demand := Iff.rfl

theorem identity (state : State) (src : Source) (fits : Fits state src)
    (same : constructors src = state.constructors) : retag state src fits = state := by
  cases state with
  | mk base view table heads catalogue bodies seed allocated reserved ordinary =>
    change constructors src = table at same
    subst table
    rfl

theorem original_context (ctx : Context) (src : Source) (fits : Fits ctx.state src)
    (cat : constructors src = ctx.state.constructors) (interp : interpretation src = ctx.interpretation) :
    context ctx.state src fits = ctx := by
  cases ctx
  unfold context
  rw [identity _ _ _ cat,interp]

def attempt (state : State) (src : Source) : Option Context :=
  if h : check state src = true then some (context state src ((check_exact state src).mp h))
  else none

theorem attempt_exact (state : State) (src : Source) :
    (∃ ctx, attempt state src = some ctx) ↔ Fits state src := by
  unfold attempt
  by_cases good : check state src = true
  · rw [dite_eq_left good]
    exact ⟨fun _ => (check_exact ..).mp good,fun _ => ⟨_,rfl⟩⟩
  · rw [dite_eq_right good]
    constructor
    · rintro ⟨_,impossible⟩; cases impossible
    · intro goodFit; exact (good ((check_exact ..).mpr goodFit)).elim


theorem attempt_identity (ctx : Context) (src : Source)
    (cat : constructors src = ctx.state.constructors) (interp : interpretation src = ctx.interpretation) :
    attempt ctx.state src = some ctx := by
  have fits : Fits ctx.state src := by
    unfold Fits
    rw [cat]
    exact ctx.state.catalogue
  unfold attempt
  rw [dite_eq_left ((check_exact ..).mpr fits),original_context ctx src _ cat interp]

end Yulang.GeneralSourceMetadataSnapshot291
