import Yulang.GeneralNominalRoleClassCompleteness251
import Yulang.GeneralNominalMixedPacket251
import Yulang.GeneralNominalJournalAppend250
namespace Yulang.GeneralNominalRoleJournalEffect251
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalRebaseJournalView243 (Effect)
open CommonNominalFullCarrier

def assemble (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax)
 (historical live : GeneralNominalRebaseClassView243.View) : Effect :=
 ⟨GeneralNominalRebaseRawView243.compile source.plan.packet.context.state env.old,
 GeneralNominalRebaseProjectionView243.compile source.plan.packet.context.state env.old (GeneralNominalPacketSupport.report source.plan.packet),
 ⟨historical.equations,
   (GeneralNominalMixedPacket251.ordinary source.plan).map (GeneralNominalRebaseRawView243.atom env.old) ++ historical.equalities⟩,
 live⟩

noncomputable def compile (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) : Option Effect :=
 (GeneralNominalRoleClass251.current source.snapshot source.plan env).bind fun historical =>
 (GeneralNominalRoleClass251.current core source.plan env).map fun live => assemble source env historical live

noncomputable def Holds (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (values : Values) : Prop :=
 GeneralNominalState.Models source.plan.packet.context.state values.old ∧
 GeneralNominalRecursiveInspection.ProjectionModels source.plan.packet.context.state (GeneralNominalPacketSupport.report source.plan.packet) values.old ∧
 GeneralNominalMixedPacket251.Ordinary source.plan values.old ∧
 GeneralNominalRoleClass251.Holds source.plan values (GeneralNominalCenteredHeadOutputs.requests source.snapshot source.plan.packet.site.occurrence) ∧
 GeneralNominalRoleClass251.Holds source.plan values (GeneralNominalCenteredHeadOutputs.requests core source.plan.packet.site.occurrence)

theorem assemble_exact (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) (assignment : Assignment)
 (historical live : GeneralNominalRebaseClassView243.View)
 (one : GeneralNominalRoleClass251.current source.snapshot source.plan env = some historical)
 (two : GeneralNominalRoleClass251.current core source.plan env = some live) :
 (assemble source env historical live).Holds assignment ↔ Holds core source (read env assignment) := by
 unfold assemble Effect.Holds GeneralNominalRebaseClassView243.View.Holds Holds
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseProjectionView243.compile_exact,
   PresenceNormalForm.all_append,GeneralNominalRebaseRawView243.all_exact,GeneralNominalMixedPacket251.ordinary_exact]
 have first := GeneralNominalRoleClass251.current_exact source.snapshot source.plan env assignment historical one
 have last := GeneralNominalRoleClass251.current_exact core source.plan env assignment live two
 constructor
 · rintro ⟨raw,projection,⟨equations,ordinary,equalities⟩,liveHeld⟩
   exact ⟨raw,projection,ordinary,first.mp ⟨equations,equalities⟩,last.mp liveHeld⟩
 · rintro ⟨raw,projection,ordinary,historicalHeld,liveHeld⟩
   have old := first.mpr historicalHeld
   exact ⟨raw,projection,⟨old.1,ordinary,old.2⟩,last.mpr liveHeld⟩

theorem compile_exact (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) (assignment : Assignment)
 (result : Effect) (success : compile core source env = some result) :
 result.Holds assignment ↔ Holds core source (read env assignment) := by
 obtain ⟨historical,one,rest⟩ := Option.bind_eq_some_iff.mp success
 obtain ⟨live,two,rfl⟩ := Option.map_eq_some_iff.mp rest
 exact assemble_exact core source env assignment historical live one two

theorem model_exact (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) (assignment : Assignment) :
 (∃ result, compile core source env = some result ∧ result.Holds assignment) ↔ Holds core source (read env assignment) := by
 constructor
 · rintro ⟨result,found,valid⟩; exact (compile_exact core source env assignment result found).mp valid
 · intro valid
   obtain ⟨historical,one,_held⟩ := (GeneralNominalRoleClassCompleteness251.model_exact source.plan env assignment _).mpr valid.2.2.2.1
   obtain ⟨live,two,_held⟩ := (GeneralNominalRoleClassCompleteness251.model_exact source.plan env assignment _).mpr valid.2.2.2.2
   refine ⟨assemble source env historical live,?_,(assemble_exact core source env assignment historical live one two).mpr valid⟩
   change (GeneralNominalRoleClass251.current source.snapshot source.plan env).bind _ = _
   change GeneralNominalRoleClass251.current source.snapshot source.plan env = some historical at one
   change GeneralNominalRoleClass251.current core source.plan env = some live at two
   simp [one,two]

noncomputable def delta (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) : Option GeneralNominalJournalAppend250.Delta :=
 (compile core source env).map fun effect => ⟨[],[],[],[effect],[]⟩

theorem delta_exact (core : GeneralNominalCenteredSteps.State roles)
 (source : GeneralNominalVersionedJournal232.Effect roles) (env : Syntax) (assignment : Assignment)
 (result : GeneralNominalJournalAppend250.Delta) (success : delta core source env = some result) :
 result.Holds assignment ↔ Holds core source (read env assignment) := by
 obtain ⟨effect,found,rfl⟩ := Option.map_eq_some_iff.mp success
 simpa [GeneralNominalJournalAppend250.Delta.Holds,PresenceNormalForm.All] using compile_exact core source env assignment effect found
end Yulang.GeneralNominalRoleJournalEffect251
