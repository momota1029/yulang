import Yulang.GeneralRebaseExecutableRequests262
import Yulang.GeneralRebaseSourceMetadata297

namespace Yulang.GeneralRebaseExecutableJournal298
open Core.PresenceGeneration (CompTerm)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseClassView243 (View equations equalities)
open GeneralNominalRebaseJournalView243 (Effect Journal)
open GeneralRebaseExecutableRequests262 (requests requests_eq)

def cls (s : GeneralNominalCenteredSteps.State roles) (f : Occurrence roles)
    (p : Plan roles) (mapping : Nat → CompTerm Nat) : View :=
  ⟨equations p mapping (requests s f),equalities mapping (requests s f)⟩

theorem cls_exact (s : GeneralNominalCenteredSteps.State roles) (f : Occurrence roles)
    (p : Plan roles) (mapping : Nat → CompTerm Nat) :
    cls s f p mapping = GeneralNominalRebaseClassView243.compile s f p mapping := by
  unfold cls GeneralNominalRebaseClassView243.compile
  rw [requests_eq]

def effect (s : State roles) (e : GeneralNominalVersionedJournal232.Effect roles)
    (mapping : Nat → CompTerm Nat) : Effect :=
  ⟨GeneralNominalRebaseRawView243.compile (GeneralNominalVersionedPlans231.privateState e.plan.packet) mapping,
    GeneralNominalRebaseProjectionView243.compile e.plan.packet.context.state mapping (GeneralNominalPacketSupport.report e.plan.packet),
    cls e.snapshot e.plan.packet.site.occurrence e.plan mapping,
    cls s.core e.plan.packet.site.occurrence e.plan mapping⟩

theorem effect_exact (s : State roles) (e : GeneralNominalVersionedJournal232.Effect roles)
    (mapping : Nat → CompTerm Nat) :
    effect s e mapping = GeneralNominalRebaseJournalView243.effect s e mapping := by
  simp only [effect,cls_exact,GeneralNominalRebaseJournalView243.effect]

def compile (s : State roles) (mapping : Nat → CompTerm Nat) : Journal :=
  ⟨GeneralNominalRebaseRawView243.compile s.core.erased.current.context.state mapping,
    GeneralNominalRebaseRawView243.compile s.core.erased.source.state mapping,
    s.core.erased.current.sites.map (GeneralNominalRebaseObservedSite243.compile · mapping),
    GeneralNominalRebaseLiveView243.compileAll s.core.sites mapping,
    s.plans.map (GeneralNominalRebasePacketView243.compile · mapping),
    s.effects.map (effect s · mapping)⟩

theorem compile_exact (s : State roles) (mapping : Nat → CompTerm Nat) :
    compile s mapping = GeneralNominalRebaseJournalView243.compile s mapping := by
  simp only [compile,GeneralNominalRebaseJournalView243.compile,effect_exact]

theorem source_models {s : State roles} {r : GeneralDeclarations.Registry} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (GeneralRebaseSourceSurvivor267.Boundary roles) r root s)
    (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (compile s mapping).Models m ↔ Models s (read mapping m) := by
  rw [compile_exact]
  exact GeneralNominalRebaseJournalView243.source_exact reached mapping m

def candidate (s : State roles) (p : Plan roles) (mapping : Nat → CompTerm Nat) :=
  (GeneralNominalRebasePacketView243.compile p mapping,cls s.core p.packet.site.occurrence p mapping)

theorem candidate_exact (s : State roles) (p : Plan roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (candidate s p mapping).1.Holds m ∧ (candidate s p mapping).2.Holds m ↔
      GeneralRebaseSignedModels297.Conditions s p (read mapping m) := by
  exact and_congr (GeneralNominalRebasePacketView243.compile_exact p mapping m)
    (by change (cls s.core p.packet.site.occurrence p mapping).Holds m ↔ _
        rw [cls_exact]
        exact GeneralNominalRebaseClassView243.compile_exact s.core _ p mapping m)

def journalReads (s : State roles) : List Nat :=
  GeneralNominalJournalSupport249.support (compile s CompTerm.var)

theorem journalReads_exact (s : State roles) :
    journalReads s = GeneralRebaseSliceJournal283.journalReads s := by
  unfold journalReads GeneralRebaseSliceJournal283.journalReads
  rw [compile_exact]

def candidateReads (s : State roles) (p : Plan roles) : List Nat :=
  GeneralNominalPacketSupport249.support (candidate s p CompTerm.var).1 ++
    GeneralNominalClassSupport249.support (candidate s p CompTerm.var).2

theorem candidateReads_exact (s : State roles) (p : Plan roles) :
    candidateReads s p = GeneralRebaseSignedSupport297.candidateReads s p := by
  unfold candidateReads candidate GeneralRebaseSignedSupport297.candidateReads
  rw [cls_exact]

end Yulang.GeneralRebaseExecutableJournal298
