import Yulang.GeneralDeclarativeWitnessReadout334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRowProjection334
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeWitnessNode334 (Generation Witness)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeWitnessReobserve334 (swap_heads receipt_grows ReaderGrowth)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)

/-- Project the *current* origin table onto the old ordinary source
slice. A row is retained only when actually present there and each
retained provenance is independently recorded by the current support
relation. This never guesses a provenance from equality in all models. -/
def restrictOrigins (base : State) {t : State} (current : Supported t done) : Supported base done where
  derivesFrom := fun e o => e ∈ base.equations ∧ current.derivesFrom e o
  ordinary := fun known => known.1

structure Embeds {s t : State} (before : Supported s once) (now : Supported t done) : Prop where
  ordinary : Extends s t
  available : (restriction before).equations ⊆ (restriction now).equations

theorem read_into_projected {s t : State} {before : Supported s once}
    {now : Supported t done} (inner : Slice before) (embedding : Embeds before now) :
    Extends (restriction inner.support) (restriction (restrictOrigins inner.base now)) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro row here
  have there := embedding.available (inner.allowed.equations here)
  obtain ⟨origin,recorded,ready⟩ := (backed_iff now row).mp there
  obtain ⟨_,original,_⟩ := (backed_iff inner.support row).mp here
  exact (backed_iff (restrictOrigins inner.base now) row).mpr
    ⟨origin,⟨inner.support.ordinary original,recorded⟩,ready⟩

theorem projected_into_now {s t : State} {before : Supported s once}
    {now : Supported t done} (old : Slice before) (h : Embeds before now) :
    Extends (restriction (restrictOrigins old.base now)) (restriction now) := by
  have atLeast := trans old.ordinary h.ordinary
  refine ⟨atLeast.constraints,atLeast.intervals,?_⟩
  intro row kept
  obtain ⟨origin,⟨_,recorded⟩,ready⟩ := (backed_iff _ row).mp kept
  exact (backed_iff now row).mpr ⟨origin,recorded,ready⟩

/-- Only the currently usable row must be reauthenticated, not every
historical occurrence of the old completion predicate or the same
old origin. Using a different origin requires an actual current
record of that same ordinary row, not an equivalent output. -/
def rebase {s t : State} {before : Supported s once} {now : Supported t done}
    (embedding : Embeds before now) (saved : Generation before r i d impl kids) :
    Generation now r i d impl kids where
  slice := ⟨saved.slice.base,restrictOrigins saved.slice.base now,
    trans saved.slice.ordinary embedding.ordinary,projected_into_now saved.slice embedding⟩
  protect := saved.protect
  fallback := saved.fallback
  targets := saved.targets
  named := saved.named
  spans := saved.spans
  source := swap_heads (read_into_projected saved.slice embedding) saved.source
  ordinary := saved.ordinary
  compiled := saved.compiled
  receipt := receipt_grows embedding.ordinary saved.receipt

theorem actual_selected {s t : State} {before : Supported s once} {now : Supported t done}
    (embedding : Embeds before now) (saved : Generation before r i d impl kids)
    (elected : Elected t r i now (candidates now r i waiting) d impl) :
    Rule now r i waiting d (.selected impl.id kids) :=
  .selected ⟨rebase embedding saved,elected⟩

theorem origins_are_sufficient {s t : State} {before : Supported s once} {now : Supported t done}
    (growth : ReaderGrowth before now) : Embeds before now := by
  refine ⟨growth.ordinary,?_⟩
  intro row observed
  obtain ⟨origin,why,done⟩ := (backed_iff before row).mp observed
  apply (backed_iff now row).mpr
  refine ⟨origin,growth.origins _ _ why,?_⟩
  cases done with
  | source => exact .source
  | completed seen => exact .completed (growth.complete _ seen)

end Yulang.GeneralDeclarativeWitnessRowProjection334
