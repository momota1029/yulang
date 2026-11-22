import Yulang.GeneralDeclarativeWitnessCompletion334

open Yulang
open GeneralDeclarativeWitnessCompletion334
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeWitnessCut334 (waiting)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeNestedExample332 (interpretation)

example : Rule (view (· = 101)) registry interpretation waiting root .pending :=
  (pending_iff_incomplete _).mpr (by decide)

example : ¬Rule (view (· = 100)) registry interpretation waiting root .pending :=
  never_pending_after (done := (· = 100)) rfl

example : Rule (view (· = 100)) registry interpretation waiting root (.selected impl.id []) :=
  (exactly_completed _).mpr (by rfl)

example : ∃ m, Models final m ∧ Evidence registry interpretation m root (.node impl.id []) :=
  (actual_dictionary_after (done := (· = 100)) rfl).2

#print axioms Yulang.GeneralDeclarativeWitnessCompletion334.backedAfter
#print axioms Yulang.GeneralDeclarativeWitnessCompletion334.exactly_completed
#print axioms Yulang.GeneralDeclarativeWitnessCompletion334.pending_iff_incomplete
#print axioms Yulang.GeneralDeclarativeWitnessCompletion334.actual_dictionary_after
