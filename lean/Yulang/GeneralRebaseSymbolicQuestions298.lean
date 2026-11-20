import Yulang.GeneralRebaseExecutableJournal298

namespace Yulang.GeneralRebaseSymbolicQuestions298
open Core.PresenceGeneration (CompTerm)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralNominalRebaseRawView243 (read Atom)
open GeneralRebaseSignedModels297 (Sign)
open GeneralRebaseSourceWitnessProgram297 (Question Holds headTest)
open GeneralRebaseMergeQuestions297 (Pair atModel aligned)
open GeneralRebaseSourceSurvivor267 (Boundary)
open CommonNominalFullCarrier (Equivalent)

structure Head where
  view : GeneralNominalRebaseRawView243.View
  projection : GeneralNominalRebaseProjectionView243.Report

def Head.Holds (h : Head) (m : Assignment) : Prop :=
  h.view.Models m ∧ h.projection.Models m

def head (p : Plan roles) (mapping : Nat → CompTerm Nat) : Head :=
  ⟨GeneralNominalRebaseRawView243.compile (GeneralNominalVersionedPlans231.privateState p.packet) mapping,
   GeneralNominalRebaseProjectionView243.compile p.packet.context.state mapping (GeneralNominalPacketSupport.report p.packet)⟩

theorem head_exact (p : Plan roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    (head p mapping).Holds m ↔ headTest p (read mapping m) := by
  exact and_congr (GeneralNominalRebaseRawView243.compile_exact ..)
    (GeneralNominalRebaseProjectionView243.compile_exact ..)

def mergeAtoms (pair : Pair roles) (mapping : Nat → CompTerm Nat) : List Atom :=
  (aligned pair).flatMap fun indices =>
    [.tyLe (mapping indices.1).ty (mapping indices.2).ty,
     .tyLe (mapping indices.2).ty (mapping indices.1).ty]

theorem merge_exact (pair : Pair roles) (mapping : Nat → CompTerm Nat) (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (mergeAtoms pair mapping) ↔
      atModel pair (read mapping m) := by
  simp only [mergeAtoms,PresenceNormalForm.All,List.forall_mem_flatMap,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,atModel,Equivalent]
  rfl

inductive Body where
 | head : Head → Body
 | install : (GeneralNominalRebasePacketView243.Packet × GeneralNominalRebaseClassView243.View) → Sign → Body
 | mergeFailure : List Atom → Body

def compile (s : State roles) (mapping : Nat → CompTerm Nat) : Question roles → Body
 | .head p => .head (head p mapping)
 | .install p sign => .install (GeneralRebaseExecutableJournal298.candidate s p mapping) sign
 | .mergeFailure pair => .mergeFailure (mergeAtoms pair mapping)

def Body.Holds (prior : Journal) (m : Assignment) : Body → Prop
 | .head data => data.Holds m
 | .install pair .pass => prior.Models m ∧ (pair.1.Holds m ∧ pair.2.Holds m)
 | .install pair .reject => prior.Models m ∧ ¬ (pair.1.Holds m ∧ pair.2.Holds m)
 | .mergeFailure atoms => prior.Models m ∧ ¬ PresenceNormalForm.All CommonNominalFullCarrier.model m atoms

theorem compile_holds {r : Registry} {s : State roles} {root : Occurrence roles}
    (path : B4TargetV8.Reachable (Boundary roles) r root s) (mapping : Nat → CompTerm Nat)
    (q : Question roles) (m : Assignment) :
    (compile s mapping q).Holds (GeneralRebaseExecutableJournal298.compile s mapping) m ↔
      Holds s q (read mapping m) := by
  have old := GeneralRebaseExecutableJournal298.source_models path mapping m
  cases q with
  | head p => exact head_exact p mapping m
  | install p sg =>
    have fit := GeneralRebaseExecutableJournal298.candidate_exact s p mapping m
    cases sg
    · exact and_congr old fit
    · exact and_congr old (not_congr fit)
  | mergeFailure pair => exact and_congr old (not_congr (merge_exact pair mapping m))

structure Program where
  prior : Journal
  jobs : List Body

def program (r : Registry) (s : State roles) (root : Occurrence roles) (checked : (Boundary roles).Checked r)
    (mapping : Nat → CompTerm Nat) : Program :=
  ⟨GeneralRebaseExecutableJournal298.compile s mapping,
    (GeneralRebaseSourceWitnessProgram297.questions r s root checked).map (compile s mapping)⟩

theorem length_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (mapping : Nat → CompTerm Nat) :
    (program r s root checked mapping).jobs.length =
      3 * (GeneralRebaseSourceQuestions297.entries r s root checked).length + s.core.sites.length * s.core.sites.length := by
  simp only [program,List.length_map,GeneralRebaseSourceWitnessProgram297.questions_size]

theorem at_index {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s) (checked : (Boundary roles).Checked r)
    (mapping : Nat → CompTerm Nat) (i : Nat) (q : Question roles)
    (recorded : (GeneralRebaseSourceWitnessProgram297.questions r s root checked)[i]? = some q)
    (m : Assignment) :
    ∃ body, (program r s root checked mapping).jobs[i]? = some body ∧
      (body.Holds (program r s root checked mapping).prior m ↔ Holds s q (read mapping m)) := by
  refine ⟨compile s mapping q,?_,compile_holds reached mapping q m⟩
  change ((GeneralRebaseSourceWitnessProgram297.questions r s root checked).map (compile s mapping))[i]? = _
  rw [List.getElem?_map,recorded,Option.map_some]

end Yulang.GeneralRebaseSymbolicQuestions298
