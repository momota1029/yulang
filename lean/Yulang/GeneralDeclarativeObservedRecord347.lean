import Yulang.GeneralDeclarativeObservedSupport347
import Yulang.GeneralDeclarativeEndpointRecord336
import Yulang.GeneralDeclarativeExactSupport337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedRecord347
open GeneralNominalState (State Models)
open GeneralDeclarativeObservedSyntax347 (rawHead structural Appears)
open GeneralDeclarativeObservedSupport347 (Record attach both_models exact_backing)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Origin Supported restriction Available)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)

/-- Stored-prefix and normalized-inline routes both retain exact
source literals. A caller may also use the exact terminal stored raw
at the next named tail slot, without choosing a tail from a model. -/
inductive Walk (s : State) (done : Nat → Prop) (author : Equation → Origin → Prop) :
    Nat → Row Expr → Expr → List Equation → Prop
  | terminal : Terminal e → Record s author ⟨root,e⟩ o → Available done o →
      Walk s done author root [] e [⟨root,e⟩]
  | inline : Terminal e → Record s author ⟨root,withTail fs e⟩ o → Available done o →
      Walk s done author root fs e [⟨root,withTail fs e⟩]
  | prepend : Record s author ⟨root,.record label (.variable field) (.variable tail)⟩ o → Available done o →
      Walk s done author tail rest e rows →
      Walk s done author root ((label,.variable field)::rest) e
        (⟨root,.record label (.variable field) (.variable tail)⟩ :: rows)

theorem rows_backed {s : State} {author : Equation → Origin → Prop}
    {rows : List Equation} (route : Walk s done author root fs e rows) :
    ∀ row ∈ rows, ∃ o, Record s author row o ∧ Available done o := by
  induction route with
  | terminal _ h available | inline _ h available =>
    intro row used
    cases List.mem_singleton.mp used
    exact ⟨_,h,available⟩
  | prepend h available _ ih =>
    intro row used
    rcases List.mem_cons.mp used with rfl|past
    · exact ⟨_,h,available⟩
    · exact ih row past

theorem surface_models {s : State} {author : Equation → Origin → Prop}
    {rows : List Equation} (route : Walk s done author root fs e rows)
    {base : GeneralDeclarativeHead320.State} (fit : Models s m)
    (valid : GeneralDeclarativeHead320.Models base m) :
    GeneralDeclarativeHead320.Models (appendFacts base rows) m :=
  both_models valid fit (fun row stored => (rows_backed route row stored).choose_spec.1.1)

theorem creates_spine {s : State} {author : Equation → Origin → Prop}
    {base : GeneralDeclarativeHead320.State} (earlier : Supported base done)
    {batch rows : List Equation} (route : Walk s done author root fs e rows)
    (embed : rows ⊆ batch) :
    Spine (restriction (attach earlier s author batch)) root fs e := by
  have atRow : ∀ row ∈ rows, row ∈ (restriction (attach earlier s author batch)).equations := by
    intro row stored
    exact (exact_backing earlier s author batch row).mpr (.inr ⟨embed stored,rows_backed route row stored⟩)
  clear embed
  induction route with
  | terminal known raw authored =>
    exact .inline (alias_refl _) known (atRow _ List.mem_cons_self)
  | inline known raw authored =>
    exact .inline (alias_refl _) known (atRow _ List.mem_cons_self)
  | prepend known authored tail ih =>
    exact .cons (alias_refl _) (atRow _ List.mem_cons_self)
      (ih (fun row found => atRow row (List.mem_cons_of_mem _ found)))

end Yulang.GeneralDeclarativeObservedRecord347
