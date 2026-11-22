import Yulang.GeneralDeclarativeJournalPrefix347
import Yulang.GeneralDeclarativeJournalRelease347
import Yulang.GeneralDeclarativeTaggedInputs340
import Yulang.GeneralDeclarativeTaggedElection340
import Yulang.GeneralDeclarativeStoppedPaired341

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereTxn348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal Models install)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralNominalRefinements (Refines)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeStoppedPaired341 (activeDemand)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeJournalPrefix347 (previous)

/-- This is the independently supported positive input of an isolated
transaction. It uses neither the legacy mixed Local nor a claim that
the two selectors agree. It is not a rejection or priority rule. -/
structure SourcePermit (r : Registry) (j : Journal rs) (p : Plan rs) where
  view : State
  done : Nat → Prop
  support : Supported view done
  waiting : Demand → GeneralDeclarations.Declaration → Prop
  models : ∀ m, Models j m → GeneralDeclarativeHead320.Models view m
  choice : Election support r p.packet.context.interpretation waiting
    (activeDemand j.mixed p.input) p.packet.declaration
  keep : List Nat
  named : State
  spans : List (Nat × GeneralDeclarativeWhere319.Capture)
  receipts : List GeneralDeclarativeEndpointOverlay336.Entry
  input : Inputs support r.constructors p.packet.context.interpretation keep view
    (activeDemand j.mixed p.input).arguments p.packet.declaration.head named spans receipts

/-- A checked boundary for an experimental transaction. The raw
refinement, current frame and model preservation are separate
obligations, not conclusions of the witness-backed election. -/
structure Txn (r : Registry) (j : Journal rs) (ctx : Context) (p : Plan rs) : Prop where
  checked : (boundary rs).Checked r
  frame : Frame (Compiled r) j.mixed.core p.packet.site.occurrence p.packet.declaration.id p
  source : Nonempty (SourcePermit r j p)
  physical : Nonempty (Refines (rawOf j) ctx.state)
  meaning : ctx.interpretation = j.mixed.core.erased.current.context.interpretation
  protects_choice : GeneralNominalCycleSteps.ChoiceCompatible j.mixed.core.erased.current p.packet
  extends_models : ∀ m, Models j m →
    ∃ n, Models (install j ctx p) n ∧
      GeneralNominalCenteredFrame179.Agree (GeneralWhereOriginSupport318.journalSources j) m n

theorem exact_models {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (t : Txn r j ctx p) (m : Assignment) :
    Models j m ↔ ∃ n, Models (install j ctx p) n ∧
      GeneralNominalCenteredFrame179.Agree (GeneralWhereOriginSupport318.journalSources j) m n := by
  constructor
  · exact t.extends_models m
  · rintro ⟨n,valid,agreement⟩
    obtain ⟨physical⟩ := t.physical
    exact (GeneralWhereOriginSupport318.journal_models j agreement).mpr
      (previous physical n valid)

end Yulang.GeneralDeclarativeWhereTxn348
