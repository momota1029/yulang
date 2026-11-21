import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeOrdinaryIncrease325
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFrameIncrease325
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeOrdinaryIncrease325 (Extends bounds alias derives supported_trace)
open GeneralDeclarativeTermWalk322 (Binds)
open GeneralDeclarativeHeadFrame325 (FromSource)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeRecordProducer325 (FieldDerives)
open GeneralDeclarativeFrameReadback325 (Frame ClauseFrame)
open CommonRoleOutermostResolver (All₂)

theorem keeps_origin {s t : State} (strengthen : Extends s t) (read : Origin s n e) : Origin t n e := by
  obtain ⟨origin,reference,stored⟩ := read
  exact ⟨origin,alias strengthen reference,strengthen.equations stored⟩

theorem keeps_fields {s t : State} (strengthen : Extends s t)
    (fields : All₂ (FieldDerives s) as bs) : All₂ (FieldDerives t) as bs := by
  induction fields with
  | nil => exact .nil
  | cons first _ ih => exact .cons ⟨first.1,derives strengthen first.2⟩ ih

theorem keeps_binds {s t : State} (strengthen : Extends s t) (binds : Binds s cap links) : Binds t cap links :=
  fun o there => derives strengthen (binds o there)

theorem keeps_head {s t : State} {old : Supported s prior} {fresh : Supported t current}
    (strengthen : Extends s t)
    (retained : (restriction old).equations ⊆ (restriction fresh).equations)
    (head : FromSource s c i old cap arg p) : FromSource t c i fresh cap arg p := by
  cases head with
  | actual written trace binds =>
    exact .actual written (supported_trace strengthen retained trace) (keeps_binds strengthen binds)
  | nominal written trace upper binds =>
    exact .nominal written (supported_trace strengthen retained trace) (derives strengthen upper)
      (keeps_binds strengthen binds)
  | record unique normal center tail order fields =>
    exact .record unique normal (keeps_origin strengthen center) (keeps_origin strengthen tail)
      order (keeps_fields strengthen fields)
  | grouped visible names compiled root capture =>
    exact .grouped visible names compiled (keeps_origin strengthen root)
      (fun n used => alias strengthen (capture n used))

theorem keeps_clause {s t : State} (strengthen : Extends s t)
    (source : ClauseFrame s r i impl cl names place) : ClauseFrame t r i impl cl names place := by
  obtain ⟨⟨codes,built,inside⟩,outputs⟩ := source
  refine ⟨⟨codes,built,?_⟩,?_⟩
  · intro pos pat e found read compound
    have h := inside pos pat e found read compound
    exact ⟨keeps_origin strengthen h.1,keeps_origin strengthen h.2.1,keeps_origin strengthen h.2.2⟩
  · intro eq used
    obtain ⟨rhs,body,read⟩ := outputs eq used
    exact ⟨rhs,body,fun notDirect => keeps_origin strengthen (read notDirect)⟩

theorem kept {s t : State} {old : Supported s prior} {fresh : Supported t current}
    (strengthen : Extends s t)
    (retained : (restriction old).equations ⊆ (restriction fresh).equations)
    (oldFrame : Frame s r i old d impl base place) : Frame t r i fresh d impl base place := by
  refine ⟨?_,fun n mentioned => bounds strengthen (oldFrame.ranges n mentioned),
    fun cl h => keeps_clause strengthen (oldFrame.clauses cl h)⟩
  exact GeneralDeclarativeNormalized320.ordered_map oldFrame.head
    (fun a p hx hy h => ⟨bounds strengthen h.1,keeps_head strengthen retained h.2⟩)

theorem old_support_after {s : State} (p : Supported s completed) (rows) (owner) :
    (restriction p).equations ⊆ (restriction (emit p owner rows)).equations := by
  intro row old
  obtain ⟨origin,source,useful⟩ := (backed_iff p row).mp old
  exact (backed_iff ..).mpr ⟨origin,.inl source,useful⟩

/-- Positive readback persists across actual ordinary output application.
This does not transport unique selection, a noncycle test, or a blocked
diagnostic: a subsequent classification must inspect these again. -/
theorem after_emit {s : State} {support : Supported s complete}
    (old : Frame s r i support d impl base place) (rows) (owner) :
    Frame (GeneralDeclarativeEntailment320.appendFacts s rows) r i (emit support owner rows)
      d impl base place :=
  kept (GeneralDeclarativeOrdinaryIncrease325.append s rows) (old_support_after support rows owner) old

end Yulang.GeneralDeclarativeFrameIncrease325
