import Yulang.GeneralDeclarativeObservedRecordExact347
import Yulang.GeneralDeclarativeCompoundSources338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedCompound347
open GeneralNominalState (State)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported Origin restriction)
open GeneralDeclarativeObservedSupport347 (attach exact_backing)
open GeneralDeclarativeObservedRecord347 (Walk rows_backed creates_spine)
open GeneralDeclarativeCompoundSources338 (Anchored Source)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row normalize residual)

private theorem closedInline {s : GeneralDeclarativeHead320.State} (fs : Row Expr) (t : Terminal e) :
    Closed s (withTail fs e) fs e := by
  induction fs with
  | nil => exact .terminal t
  | cons h next ih =>
    rcases h with ⟨k,v⟩
    exact .field ih

/-- Recover the exact *first authored RHS*, and a spine for that
expression, from a real physical record walk. A named tail is followed
at its own head. This is stronger than an equality to the flattened
record, and introduces no new authored fact. -/
theorem first_source {raw : State} {base : GeneralDeclarativeHead320.State}
    {author : Equation → Origin → Prop} (prior : Supported base done)
    {rows batch : List Equation} (route : Walk raw done author key fs ending rows)
    (place : rows ⊆ batch) :
    ∃ rhs, Anchored (restriction (attach prior raw author batch)) key rhs ∧
      Closed (restriction (attach prior raw author batch)) rhs fs ending := by
  have recorded : ∀ row ∈ rows, row ∈ (restriction (attach prior raw author batch)).equations := by
    intro row part
    exact (exact_backing prior raw author batch row).mpr (.inr ⟨place part,rows_backed route row part⟩)
  cases route with
  | terminal e h found =>
    exact ⟨_,⟨_,alias_refl _,recorded _ List.mem_cons_self⟩,.terminal e⟩
  | inline e h found =>
    exact ⟨_,⟨_,alias_refl _,recorded _ List.mem_cons_self⟩,closedInline _ e⟩
  | prepend h found remaining =>
    have tail := creates_spine prior remaining (fun _ used => place (List.mem_cons_of_mem _ used))
    exact ⟨_,⟨_,alias_refl _,recorded _ List.mem_cons_self⟩,.field (.name tail)⟩

open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeCompoundPattern338 (peel)
open GeneralDeclarativeCompoundTree338 (World Tree TreeExact)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)

/-- Feed both independently observed source routes into the actual
recursive compound compiler. Compound descendants use the compiler's
existing source judgment at their *exact* visible payloads; none
are selected or read solely from the final model. -/
theorem compile {raw : State} {base : GeneralDeclarativeHead320.State}
    {author : Equation → Origin → Prop} (prior : Supported base done)
    (arg : Capture) (pat : Pattern) (keep : List Nat)
    {lowRows highRows : List Equation}
    (lower : Walk raw done author arg.lower ls le lowRows)
    (upper : Walk raw done author arg.upper us ue highRows)
    (split : peel pat = (fs,tail)) (nonempty : fs ≠ []) (distinct : (fs.map Prod.fst).Nodup)
    (loKeys : ∀ k ∈ fs.map Prod.fst, ∃ a, (k,a) ∈ normalize ls)
    (hiKeys : ∀ k ∈ fs.map Prod.fst, ∃ a, (k,a) ∈ normalize us)
    (valid : Bounds base arg) :
    let small := attach prior raw author (lowRows++highRows)
    let w : World done := ⟨_,small,[]⟩
    (∀ f ∈ fs, ∀ a b, (f.1,a) ∈ normalize ls → (f.1,b) ∈ normalize us → Source (restriction small) a b f.2) →
    Source (restriction small) (withTail (residual (fs.map Prod.fst) (normalize ls)) le)
      (withTail (residual (fs.map Prod.fst) (normalize us)) ue) tail →
    ∃ final uses, Tree keep w arg pat final uses ∧ TreeExact keep w pat final uses := by
  dsimp only
  intro payloads last
  obtain ⟨a,left,scannedLo⟩ := first_source prior lower (fun _ used => List.mem_append_left highRows used)
  obtain ⟨b,right,scannedHi⟩ := first_source prior upper (fun _ used => List.mem_append_right lowRows used)
  have source : Source (restriction (attach prior raw author (lowRows++highRows))) a b pat :=
    .record split nonempty distinct scannedLo scannedHi loKeys hiKeys payloads last
  exact GeneralDeclarativeCompoundSources338.exact source keep ⟨left,right⟩ valid

end Yulang.GeneralDeclarativeObservedCompound347
